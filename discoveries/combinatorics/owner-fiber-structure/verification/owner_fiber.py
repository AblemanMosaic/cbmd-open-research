"""Standalone owner-fiber verifier. Standard library only; imports nothing from the archive.

Checks the three parts of the candidate claim, each with an adverse control that
must fail, and refuses to report success on a degenerate parameter box.

  U1  unique contributor      : a fixed covered target and owner have at most one
                                nonzero contributing source row
  U2  class-count bound       : for a multiset of targets, contributors per owner are
                                at most the number of distinct orbit classes present
  U3  active-coordinate need  : head coherence is required on the target's ACTIVE
                                coordinates; dropping it at one admits two contributors

Degeneracy gate.  With A = 0 and R >= |D(u)| every off-diagonal source row is
identically zero, so U1 holds vacuously and the box tests nothing.  This was the
original defect in the predecessor evidence.  The run FAILS unless off-diagonal
contributors actually occur.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction
from itertools import combinations, product
from math import comb as _comb


# ---------------------------------------------------------------- arithmetic
def comb(n: int, k: int) -> int:
    if k < 0 or (n >= 0 and k > n):
        return 0
    if n < 0:
        return (-1) ** k * _comb(-n + k - 1, k)
    return _comb(n, k)


def amplitude(A: int, R: int, delta: int, f: int) -> int:
    """Integer numerator; depends only on (A, R, |D|, |E|-1)."""
    d = R - 1 - f
    N = A + R - delta
    total = sum(comb(N, k) * (1 if d - k == 0 else comb(A + d - k - 1, d - k))
                for k in range(d + 1))
    return (-1) ** A * total * 2 ** (R - 1)


# ---------------------------------------------------------------- the model
def active(u: tuple[int, ...], Q: int) -> list[int]:
    return [t for t in range(Q) if u[t] != u[Q + t]]


def in_orbit(u: tuple[int, ...], y: tuple[int, ...], Q: int) -> bool:
    return all({y[t], y[Q + t]} == {u[t], u[Q + t]} for t in range(Q))


def mismatches(u: tuple[int, ...], y: tuple[int, ...], Q: int) -> list[int]:
    return [t for t in range(Q) if y[t] != u[Q + t]]


def source_row(u: tuple[int, ...], y: tuple[int, ...], A: int, R: int, Q: int) -> tuple[Fraction, ...]:
    """[y=u] - (n / 2^(R-1)) * (1 - prod_{s in E} (1 - x/(s+1))), as a coefficient tuple."""
    out = [Fraction(1 if y == u else 0)]
    if not in_orbit(u, y, Q):
        return tuple(out)
    E = mismatches(u, y, Q)
    if not E or len(E) > R:
        return tuple(out)
    n = amplitude(A, R, len(active(u, Q)), len(E) - 1)
    if n == 0:
        return tuple(out)
    prod = [Fraction(1)]
    for s in E:
        nxt = [Fraction(0)] * (len(prod) + 1)
        for i, value in enumerate(prod):
            nxt[i] += value
            nxt[i + 1] -= value / (s + 1)
        prod = nxt
    phi = [-value for value in prod]
    phi[0] += 1                                   # 1 - prod
    scale = Fraction(n, 2 ** max(R - 1, 0))
    row = [Fraction(0)] * max(len(out), len(phi))
    for i, value in enumerate(out):
        row[i] += value
    for i, value in enumerate(phi):
        row[i] -= scale * value
    while len(row) > 1 and row[-1] == 0:
        row.pop()
    return tuple(row)


def nonzero(row: tuple[Fraction, ...]) -> bool:
    return any(row)


def candidate(u: tuple[int, ...], head: tuple[int, ...], Q: int) -> tuple[int, ...] | None:
    """The unique orbit element with the requested head, or None."""
    slot = []
    for t in range(Q):
        a, d, h = u[t], u[Q + t], head[t]
        if h != a and h != d:
            return None
        slot.append(d if h == a else a)
    return tuple(head) + tuple(slot)


# ---------------------------------------------------------------- layouts
def layouts(Q: int, r: int, owners_count: int, seed: int, coherent: bool = True,
            break_active: bool = False):
    """Deterministic pseudo-random layouts. Each column carries a universal type and an owner;
    heads[v] is the owner's head word. Coherence ties a column's head to its owner's head."""
    state = seed
    def nxt(m):
        nonlocal state
        state = (1103515245 * state + 12345) % (1 << 31)
        return state % m
    types = list(product(range(r), repeat=2 * Q))
    # Heads must COVER the head-word space, or the only orbit element carrying an
    # owner's head is the target itself and no off-diagonal contributor can ever
    # appear. The surplus owners duplicate heads on purpose: distinct owners with
    # equal head words are exactly the case the owner check exists to handle.
    words = list(product(range(r), repeat=Q))
    heads = [words[i % len(words)] for i in range(max(owners_count, len(words)))]
    owners_count = len(heads)
    columns = []
    for y in types:
        if coherent:
            cands = [v for v in range(owners_count) if heads[v] == y[:Q]]
            if not cands:
                continue
            columns.append((y, cands[nxt(len(cands))]))
        else:
            columns.append((y, nxt(owners_count)))
    return heads, columns


def contributors(u, columns, owner, A, R, Q):
    return [y for (y, own) in columns if own == owner and nonzero(source_row(u, y, A, R, Q))]


# ---------------------------------------------------------------- checks
def check_U1(Q, r, A, R, owners_count, trials):
    stats = {"fibers": 0, "offdiagonal_contributors": 0, "violations": 0,
             "fibers_with_one": 0, "candidate_agreements": 0, "candidate_mismatches": 0}
    worst = None
    for seed in range(trials):
        heads, columns = layouts(Q, r, owners_count, seed)
        for (u, _) in columns:
            for v in range(len(heads)):
                stats["fibers"] += 1
                got = contributors(u, columns, v, A, R, Q)
                for y in got:
                    if y != u:
                        stats["offdiagonal_contributors"] += 1
                if len(got) > 1:
                    stats["violations"] += 1
                    worst = worst or {"target": list(u), "owner": v,
                                      "contributors": [list(y) for y in got]}
                elif len(got) == 1:
                    stats["fibers_with_one"] += 1
                    predicted = candidate(u, heads[v], Q)
                    if predicted == got[0]:
                        stats["candidate_agreements"] += 1
                    else:
                        stats["candidate_mismatches"] += 1
    stats["first_violation"] = worst
    return stats


def check_U2(Q, r, A, R, owners_count, trials, max_targets=3):
    """Contributors to a sum of target rows, against the orbit-class count."""
    stats = {"sums": 0, "violations": 0, "tight": 0}
    worst = None
    for seed in range(trials):
        heads, columns = layouts(Q, r, owners_count, seed)
        allowed = [y for (y, _) in columns]
        owners_count = len(heads)
        for k in range(1, max_targets + 1):
            for targets in combinations(allowed[: min(len(allowed), 6)], k):
                classes = {tuple(frozenset((u[t], u[Q + t])) for t in range(Q)) for u in targets}
                for v in range(owners_count):
                    stats["sums"] += 1
                    count = 0
                    for (y, own) in columns:
                        if own != v:
                            continue
                        total = [Fraction(0)]
                        for u in targets:
                            row = source_row(u, y, A, R, Q)
                            if len(row) > len(total):
                                total += [Fraction(0)] * (len(row) - len(total))
                            for i, value in enumerate(row):
                                total[i] += value
                        if any(total):
                            count += 1
                    if count > len(classes):
                        stats["violations"] += 1
                        worst = worst or {"targets": [list(u) for u in targets],
                                          "owner": v, "contributors": count,
                                          "classes": len(classes)}
                    elif count == len(classes) and count >= 2:
                        stats["tight"] += 1
    stats["first_violation"] = worst
    return stats


def check_U3(Q, r, A, R):
    """Adverse control: break coherence at one ACTIVE coordinate and find two contributors."""
    types = list(product(range(r), repeat=2 * Q))
    for u in types:
        D = active(u, Q)
        if not D:
            continue
        t0 = min(D)
        columns = []
        for y in types:
            if in_orbit(u, y, Q) and all(y[t] == u[t] for t in D if t != t0):
                columns.append((y, 0))        # one owner claims a coherence-broken family
            else:
                columns.append((y, 1))
        got = contributors(u, columns, 0, A, R, Q)
        if len(got) >= 2:
            return {"found": True, "target": list(u), "broken_active_coordinate": t0,
                    "contributors": [list(y) for y in got[:4]], "count": len(got)}
    return {"found": False}


def degeneracy(Q, r, A, R):
    """Off-diagonal orbit columns with a nonzero row, over all targets."""
    types = list(product(range(r), repeat=2 * Q))
    cand = nz = 0
    for u in types:
        for y in types:
            if y == u or not in_orbit(u, y, Q):
                continue
            E = mismatches(u, y, Q)
            if not (1 <= len(E) <= R):
                continue
            cand += 1
            if nonzero(source_row(u, y, A, R, Q)):
                nz += 1
    return {"offdiagonal_candidates": cand, "offdiagonal_nonzero": nz,
            "status": "DEGENERATE_DIAGONAL_ONLY" if cand and nz == 0 else "NONDEGENERATE"}


def main() -> int:
    Q, r, owners_count, trials = 2, 2, 5, 6   # 4 head words + 1 duplicate (head collision)
    live = {"A": 1, "R": 2}            # non-degenerate: A >= 1
    dead = {"A": 0, "R": 3}            # the original defect regime: A = 0, R >= |D|
    report = {
        "schema": "cbmd.owner-fiber-standalone.v1",
        "box": {"Q": Q, "r": r, "owners": owners_count, "layout_seeds": trials, **live},
        "degeneracy_live": degeneracy(Q, r, **live),
        "degeneracy_defect_regime": degeneracy(Q, r, **dead),
        "U1_unique_contributor": check_U1(Q, r, live["A"], live["R"], owners_count, trials),
        "U2_class_count_bound": check_U2(Q, r, live["A"], live["R"], owners_count, trials),
        "U3_active_coherence_necessary": check_U3(Q, r, live["A"], live["R"]),
        "U1_breadth_Q3": {"box": {"Q": 3, "r": 2, "A": 1, "R": 2, "seeds": 3},
                          "degeneracy": degeneracy(3, 2, 1, 2),
                          **check_U1(3, 2, 1, 2, 9, 3)},
        "nonclaims": [
            "a finite model of the owner-fiber statement; no binding to the packed source definitions",
            "no native SAT consequence, no refinement proof, no novelty determination",
            "block structure is modelled as a single covered target block",
        ],
        "authority_effect": "NONE",
    }
    gates = []
    if report["degeneracy_live"]["status"] != "NONDEGENERATE":
        gates.append("live parameter box is degenerate; the checks would be vacuous")
    if report["degeneracy_defect_regime"]["status"] != "DEGENERATE_DIAGONAL_ONLY":
        gates.append("the known A=0 defect regime did not reproduce as degenerate")
    u1 = report["U1_unique_contributor"]
    if u1["violations"]:
        gates.append(f"U1 violated {u1['violations']} times")
    if u1["offdiagonal_contributors"] == 0:
        gates.append("U1 exercised no off-diagonal contributor")
    if u1["candidate_mismatches"]:
        gates.append(f"candidate lookup disagreed {u1['candidate_mismatches']} times")
    b3 = report["U1_breadth_Q3"]
    if b3["violations"] or b3["candidate_mismatches"]:
        gates.append("U1 breadth pass at Q=3 failed")
    if b3["offdiagonal_contributors"] == 0:
        gates.append("U1 breadth pass exercised no off-diagonal contributor")
    u2 = report["U2_class_count_bound"]
    if u2["violations"]:
        gates.append(f"U2 violated {u2['violations']} times")
    if u2["tight"] == 0:
        gates.append("U2 bound never attained; sharpness untested")
    if not report["U3_active_coherence_necessary"]["found"]:
        gates.append("U3 adverse control found no two-contributor witness")
    report["content_gate_failures"] = gates
    report["status"] = "PASS" if not gates else "FAIL"
    print(json.dumps(report, indent=1))
    return 0 if not gates else 1


if __name__ == "__main__":
    raise SystemExit(main())
