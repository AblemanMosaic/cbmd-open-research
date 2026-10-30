"""Two consumers per place suffice for hardness (revision 0.16.0).

Conflict-free nets (one consumer per place, every transition with an input) are
polynomial (0.12.0, compiled 0.13.0/0.15.0).  Revision 0.10.0 put all conflict
on one place `g` with many consumers.  Here `g` is split into copies
g_0..g_{L-1}, L = n + K, one per former reader, joined by a CYCLIC chain of
copier transitions g_j -> g_{(j+1) mod L}.  A copier is enabled as soon as its
input holds and can only be blocked by its output holding, so one copy holding
forces all of them.  Every place then has at most two consumers, the net is
strict free-choice, every capacity is 1.  Lean: `DegreeTwo.lean`,
`degreeTwo_preserves_iff_unsatisfiable` (for 2 <= n + K).

The cycle is essential, and the census found that out: with an open chain
g_0 -> ... -> g_{L-1}, a bad marking can switch on a suffix of the chain only,
leaving the earlier clauses unconstrained. The first draft used an open chain
and gave wrong verdicts; the `open` ablation below keeps that failure on record.

Gates: exact against a brute-force SAT oracle, judged by a direct search for a
bad marking; both outcomes; every net strict free-choice with at most two
consumers per place; bridge against a transcription of the Lean `dpre`/`dpost`;
ablations (no copiers; an OPEN copier chain) must each give wrong verdicts.
"""
from __future__ import annotations

import json
import os
import random
import sys
from itertools import combinations_with_replacement

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hardness import all_clauses, random_cnf, satisfiable  # noqa: E402
from free_choice import strict_free_choice  # noqa: E402
from marked_graph import brute  # noqa: E402


def d2_net(n, clauses, copiers="cyclic"):
    """Transitions in the Lean order: variable i, user n+j, copier n+L+j."""
    K = len(clauses)
    L = n + K
    P = 2 * n + L
    pre, post = [], []

    def t(ins, outs):
        a = [0] * P
        b = [0] * P
        for q in ins:
            a[q] = 1
        for q in outs:
            b[q] = 1
        pre.append(a)
        post.append(b)
    for i in range(n):
        t([i, n + i], [])
    for j in range(L):
        if j < n:
            t([2 * n + j], [j, n + j])
        else:
            t([2 * n + j], [abs(l) - 1 if l > 0 else n + abs(l) - 1 for l in clauses[j - n]])
    for j in range(L):
        if copiers == "cyclic" or (copiers == "open" and j + 1 < L):
            t([2 * n + j], [2 * n + (j + 1) % L])
    return pre, post, [1] * P, P, len(pre)


def lean_rows(n, clauses):
    K = len(clauses)
    L = n + K
    P = 2 * n + L
    rows = []
    for c in range(n + L + L):
        if c < n:
            pre = [int(q == c or q == n + c) for q in range(P)]
        elif c < n + L:
            pre = [int(q == 2 * n + (c - n)) for q in range(P)]
        else:
            pre = [int(q == 2 * n + (c - n - L)) for q in range(P)]
        post = []
        for q in range(P):
            if c < n:
                post.append(0)
            elif c < 2 * n:
                post.append(int(q == c - n or q == n + (c - n)))
            elif c < n + L:
                cl = clauses[c - 2 * n]
                post.append(int((q + 1) in cl) if q < n else int(-(q - n + 1) in cl) if q < 2 * n else 0)
            else:
                post.append(int(q == 2 * n + (c - n - L + 1) % L))
        rows.append((tuple(pre), tuple(post)))
    return sorted(rows)


def population(trials=60, seed=3):
    pool = [(2, [list(c) for c in cnf]) for m in range(0, 4)
            for cnf in combinations_with_replacement(all_clauses(2, 2), m)]
    rng = random.Random(seed)
    for _ in range(trials):
        n = rng.randint(2, 3)
        pool.append((n, random_cnf(rng, n, rng.randint(1, 2 * n), rng.choice([2, 3]))))
    return pool


def run(trials=60):
    agree = disagree = sat = unsat = shape_bad = bridge_bad = abl_none = abl_open = 0
    maxc = set()
    for n, cnf in population(trials):
        pre, post, cap, P, T = d2_net(n, cnf)
        mc = max(sum(1 for t in range(T) if pre[t][q]) for q in range(P))
        maxc.add(mc)
        shape_bad += (not strict_free_choice(pre, P, T)) or mc > 2
        bridge_bad += sorted(zip(map(tuple, pre), map(tuple, post))) != lean_rows(n, cnf)
        v = brute(pre, post, cap, P, T)
        s = satisfiable(n, cnf)
        sat += s
        unsat += not s
        agree += v == (not s)
        disagree += v != (not s)
        abl_none += brute(*d2_net(n, cnf, "none")) != (not s)
        abl_open += brute(*d2_net(n, cnf, "open")) != (not s)
    gates = {
        "reduction_is_exact": disagree == 0 and agree > 0,
        "both_outcomes_occur": sat > 0 and unsat > 0,
        "strict_free_choice_at_most_two_consumers": shape_bad == 0 and maxc == {2},
        "bridge_matches_lean": bridge_bad == 0,
        "ablation_no_copiers_breaks": abl_none > 0,
        "ablation_open_chain_breaks": abl_open > 0,
    }
    return {"schema": "cbmd.petri-degree-two-hardness.v1", "formulas": agree + disagree,
            "agree": agree, "disagree": disagree, "satisfiable": sat, "unsatisfiable": unsat,
            "max_consumers_per_place": sorted(maxc), "bridge_mismatches": bridge_bad,
            "ablation_no_copiers_wrong": abl_none, "ablation_open_chain_wrong": abl_open,
            "gates": gates, "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["the reduction's correctness is compiled; coNP membership and polynomial running time are written arguments"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 60)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
