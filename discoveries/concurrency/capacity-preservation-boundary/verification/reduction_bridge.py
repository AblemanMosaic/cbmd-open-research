"""Bridge: the Lean reduction (Reduction.lean, Guard.lean) builds the same net
as hardness.py.

Revision 0.9.0 compiles `preserves_iff_unsatisfiable`.  A compiled theorem
about a different net than the one the census tested would certify nothing
about the census, so this script transcribes the Lean definitions `gneg`,
`gpos`, `net` and `cap` literally and compares, formula by formula, against
`hardness.build(*hardness.guarded_cnf(...))`:

  * the capacity vectors are equal;
  * the transitions are equal as a MULTISET of (pre, post) rows.  Lean groups
    the guard clauses by family, hardness.py interleaves them per variable;
    `Preserves` quantifies over all transitions, so order is immaterial;
  * a deliberately wrong transcription (negative literals of G kept on x_a
    instead of moved to xbar_a) must be DETECTED, or the comparison is idle;
  * Lean's `NoTautology` hypothesis holds of every guarded CNF (checked on the
    encoded clause list itself, not inferred).

Gates: zero mismatches over the exhaustive box and the random pass, and a
non-empty population of each.
"""
from __future__ import annotations

import json
import os
import random
import sys
from itertools import combinations_with_replacement

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hardness import all_clauses, build, guarded_cnf, random_cnf  # noqa: E402


def lean_cnf(n, clauses):
    """G as Lean's CNF: neg[c][a], pos[c][a] booleans."""
    neg = [[False] * n for _ in clauses]
    pos = [[False] * n for _ in clauses]
    for c, cl in enumerate(clauses):
        for lit in cl:
            (pos if lit > 0 else neg)[c][abs(lit) - 1] = True
    return neg, pos


def gneg(n, K, c, a):
    if c < n: return a == c or a == n + c
    if c < n + n: return a == n + n
    if c < n + n + n: return a == c - (n + n)
    if c < n + n + n + n: return a == n + (c - (n + n + n))
    return a == n + n


MUTATE = False   # negative control: rewrite NOT x_a as x_a instead of xbar_a


def gpos(n, K, G, c, a):
    neg, pos = G
    if MUTATE and c >= n + n + n + n and a < n:
        k = c - (n + n + n + n)
        return pos[k][a] or neg[k][a]
    if c < n: return False
    if c < n + n: return a == c - n or a == n + (c - n)
    if c < n + n + n + n: return a == n + n
    k = c - (n + n + n + n)
    if k < K:
        if a < n: return pos[k][a]
        if a < n + n: return neg[k][a - n]
        return False
    return False


def lean_net(n, clauses):
    K = len(clauses)
    G = lean_cnf(n, clauses)
    A = n + n + 1
    P = A + 1
    rows = []
    for c in range(n + n + n + n + K):          # clause transitions
        pre = [int(gneg(n, K, c, a)) for a in range(A)] + [0]
        post = [int(gpos(n, K, G, c, a)) for a in range(A)] + [0]
        rows.append((tuple(pre), tuple(post)))
    for b in range(A):                          # probes
        pre = [int(a == b) for a in range(A)] + [0]
        post = [0] * A + [1]
        rows.append((tuple(pre), tuple(post)))
    cap = [1] * A + [0]
    no_taut = all(not (gneg(n, K, c, a) and gpos(n, K, G, c, a))
                  for c in range(n + n + n + n + K) for a in range(A))
    return sorted(rows), cap, P, no_taut


def compare(n, clauses):
    rows, cap, P, no_taut = lean_net(n, clauses)
    pre, post, hcap, hP, _T = build(*guarded_cnf(n, clauses))
    hrows = sorted((tuple(a), tuple(b)) for a, b in zip(pre, post))
    return rows == hrows and cap == hcap and P == hP, no_taut


def run(trials=240, seed=1030):
    formulas = mismatches = taut = 0
    samples = []
    clauses_all = all_clauses(2, 2)
    pool = [[list(c) for c in cnf] for m in range(1, 4)
            for cnf in combinations_with_replacement(clauses_all, m)]
    rng = random.Random(seed)
    for _ in range(trials):
        n = rng.randint(2, 3)
        mode = rng.randint(0, 1)
        pool.append(random_cnf(rng, n, rng.randint(1, 3) if mode == 0
                               else rng.randint(3 * n, 6 * n), rng.choice([2, 3])))
    for cnf in pool:
        n = max(abs(l) for cl in cnf for l in cl)
        n = max(n, 2)
        same, nt = compare(n, cnf)
        formulas += 1
        mismatches += not same
        taut += not nt
        if not same and len(samples) < 3:
            samples.append(cnf)
    global MUTATE
    MUTATE = True
    mutant_mismatches = sum(not compare(max(max(abs(l) for cl in cnf for l in cl), 2), cnf)[0]
                            for cnf in pool)
    MUTATE = False
    gates = {"nets_identical": mismatches == 0,
             "control_detects_mutated_encoding": mutant_mismatches > 0,
             "no_tautology_holds": taut == 0,
             "population_nonempty": formulas > 0}
    return {"schema": "cbmd.petri-reduction-bridge.v1", "formulas": formulas,
            "mismatches": mismatches, "mutant_mismatches": mutant_mismatches, "no_tautology_failures": taut,
            "samples": samples, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["checks that the compiled theorem is about the census's net; "
                          "it does not re-prove the theorem"]}


if __name__ == "__main__":
    out = run()
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
