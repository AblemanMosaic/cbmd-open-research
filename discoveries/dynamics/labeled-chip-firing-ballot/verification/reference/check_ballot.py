"""Labeled chip-firing on undirected k-ary trees: the ballot conjecture fails from 31 chips (k = 2).

Model (Musiker-Nguyen; Inagaki-Khovanova-Luo, arXiv 2410.00039; Inagaki-Lin,
arXiv 2509.17358): infinite k-ary tree, root with a self-loop, N = (k^l - 1)/(k - 1)
labeled chips 1..N on the root. A vertex with at least k + 1 chips may fire: it
chooses any k + 1 of its chips, sorts them, sends the ceil((k+1)/2)-th smallest
to its parent (the root keeps it) and the others, in increasing order, to its
children 1..k. Indexing: root 0, children of v are k v + 1, ..., k v + k.

Ballot property (IKL Definition 2 / Conjecture 3.7 for k = 2; Inagaki-Lin
Conjecture 5.1 for k-ary trees): in every stable configuration, for every
vertex v and children a < b, the i-th smallest chip in the subtree of child a
is smaller than the i-th smallest chip in the subtree of child b, for all i.

Gates (each required):
  * CERTIFICATES_REPLAY: each certificate in counterexamples.json is a legal
    firing sequence from N chips on the root (every firing uses k + 1 chips
    present at a vertex with at least k + 1 chips), ends stable with one chip
    per vertex of the first l levels, matches its recorded final configuration,
    and violates the ballot property; cases (k, l) = (2,5) twice (one violation
    at the root), (2,6), (2,7), (3,4), (4,4);
  * THRESHOLD_EQUIVALENCE: for equal-size sets A, B, "i-th smallest of A < i-th
    smallest of B for all i" iff "|A cap [1,t]| >= |B cap [1,t]| for all t"
    (checked exhaustively on all pairs of disjoint 3-subsets of 1..8 and
    4-subsets of 1..9);
  * POSITIVE_CASES: in the two-colour projection (chips <= t red), every run
    reaches only stable states with red-count dominance at every vertex, for
    every threshold t, in the cases (k, l) = (2, 2), (2, 3), (2, 4), (3, 2),
    (3, 3), (4, 3) -- hence the ballot property holds for all stable
    configurations in those cases;
  * CONTROL: altering one firing of a certificate makes the replay fail.
"""
from __future__ import annotations
import itertools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def replay(k, L, firings):
    N = sum(k ** i for i in range(L))
    NV = sum(k ** i for i in range(L + 2))
    P = (k + 2) // 2
    chips = {v: set() for v in range(NV)}
    chips[0] = set(range(1, N + 1))
    for v, pick in firings:
        if len(chips[v]) < k + 1 or len(pick) != k + 1 or not set(pick) <= chips[v]:
            return None
        chips[v] -= set(pick)
        child = 0
        for pos, x in enumerate(sorted(pick), 1):
            if pos == P:
                chips[0 if v == 0 else (v - 1) // k].add(x)
            else:
                child += 1
                chips[k * v + child].add(x)
    if any(len(c) > k for c in chips.values()):
        return None
    occ = {v: c for v, c in chips.items() if c}
    if sorted(occ) != list(range(N)) or any(len(c) != 1 for c in occ.values()):
        return None
    return [min(occ[v]) for v in range(N)]


def violations(k, final):
    N = len(final)
    def sub(v):
        return [] if v >= N else [final[v]] + [x for c in range(1, k + 1) for x in sub(k * v + c)]
    out = []
    for v in range(N):
        if k * v + k < N:
            S = [sorted(sub(k * v + c)) for c in range(1, k + 1)]
            for a in range(k):
                for b in range(a + 1, k):
                    if any(x > y for x, y in zip(S[a], S[b])):
                        out.append((v, a + 1, b + 1))
    return out


def threshold_equivalence():
    for n, m in ((8, 3), (9, 4)):
        for A in itertools.combinations(range(1, n + 1), m):
            rest = [x for x in range(1, n + 1) if x not in A]
            for B in itertools.combinations(rest, m):
                ballot = all(a < b for a, b in zip(sorted(A), sorted(B)))
                dom = all(sum(x <= t for x in A) >= sum(x <= t for x in B) for t in range(1, n + 1))
                if ballot != dom:
                    return False
    return True


def colour_exhaustive(k, L):
    N = sum(k ** i for i in range(L))
    NV = sum(k ** i for i in range(L + 2))
    P = (k + 2) // 2
    for T in range(1, N):
        start = tuple([T, N - T] + [0] * (2 * NV - 2))
        seen = {start}
        stack = [start]
        while stack:
            s = stack.pop()
            any_move = False
            for v in range(NV):
                R, B = s[2 * v], s[2 * v + 1]
                if R + B < k + 1:
                    continue
                if k * v + k >= NV:
                    return False
                any_move = True
                for r in range(max(0, k + 1 - B), min(k + 1, R) + 1):
                    t = list(s)
                    t[2 * v] -= r
                    t[2 * v + 1] -= k + 1 - r
                    child = 0
                    for pos in range(1, k + 2):
                        red = pos <= r
                        if pos == P:
                            d = 0 if v == 0 else (v - 1) // k
                        else:
                            child += 1
                            d = k * v + child
                        t[2 * d + (0 if red else 1)] += 1
                    t = tuple(t)
                    if t not in seen:
                        seen.add(t)
                        stack.append(t)
            if not any_move:
                sub = [0] * NV
                for v in range(NV - 1, -1, -1):
                    sub[v] = s[2 * v] + sum(sub[k * v + c] for c in range(1, k + 1) if k * v + c < NV)
                for v in range(NV):
                    if k * v + k < NV:
                        for a in range(1, k + 1):
                            for b in range(a + 1, k + 1):
                                if sub[k * v + a] < sub[k * v + b]:
                                    return False
    return True


def main():
    data = json.loads((HERE / "counterexamples.json").read_text())
    rep_ok = True
    cases = []
    for c in data["certificates"]:
        fin = replay(c["k"], c["levels"], c["firings"])
        viol = violations(c["k"], fin) if fin else []
        ok = fin is not None and fin == c["final"] and bool(viol)
        rep_ok &= ok
        cases.append({"k": c["k"], "levels": c["levels"], "chips": c["chips"], "firings": len(c["firings"]),
                      "violations": viol[:5], "ok": ok})
    c0 = data["certificates"][0]
    bad = [list(f) for f in c0["firings"]]
    bad[10] = [bad[10][0], sorted(set(range(1, c0["chips"] + 1)) - set(bad[10][1]))[:3]]
    control = replay(c0["k"], c0["levels"], bad) != c0["final"]
    gates = {
        "CERTIFICATES_REPLAY": rep_ok,
        "THRESHOLD_EQUIVALENCE": threshold_equivalence(),
        "POSITIVE_CASES": all(colour_exhaustive(k, L) for k, L in ((2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (4, 3))),
        "CONTROL_altered_firing_fails": control,
    }
    out = {"schema": "cbmd.labeled-chip-firing.ballot.v1", "cases": cases, "gates": gates,
           "status": "PASS" if all(gates.values()) else "FAIL", "authority_effect": "NONE"}
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
