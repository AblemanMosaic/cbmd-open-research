"""Input-less transitions make conflict-free nets coNP-hard (revision 0.14.0).

Revision 0.12.0 decides preservation for conflict-free nets in which every
transition has an input place.  This shows that hypothesis is exactly what
makes them tractable.  For a CNF on n variables: places x+_i, x-_i (capacity
1); a transition x+_i, x-_i -> (nothing) per variable; and, per clause, an
INPUT-LESS transition producing into its literal places.  Each place has one
consumer, so the net is conflict-free.  Lean: `InputLess.lean`,
`inputless_preserves_iff_unsatisfiable` (for at least one clause).

Gates (each required):
  * exact against a brute-force SAT oracle, judged by `petri.preserves`;
  * both outcomes occur;
  * every net is conflict-free and has an input-less transition, checked;
  * BRIDGE: the net equals a transcription of the Lean `ipre`/`ipost`;
  * ABLATION: dropping the variable transitions must break exactness;
  * the revision 0.12.0 procedure, applied outside its hypothesis to these
    nets, must give wrong verdicts -- these nets are a structured witness of
    the failure the 0.12.0 census measured at random;
  * the stated exception: with no clauses the net preserves although the empty
    CNF is satisfiable, which is why the theorem assumes a clause.
"""
from __future__ import annotations

import json
import os
import random
import sys
from itertools import combinations_with_replacement

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from petri import preserves  # noqa: E402
from hardness import all_clauses, random_cnf, satisfiable  # noqa: E402
from conflict_free import conflict_places, decide as cf_decide  # noqa: E402


def il_net(n, clauses, drop_var=False):
    P = 2 * n
    pre, post = [], []
    if not drop_var:
        for i in range(n):
            a = [0] * P
            a[i] = a[n + i] = 1
            pre.append(a)
            post.append([0] * P)
    for cl in clauses:
        b = [0] * P
        for l in cl:
            b[abs(l) - 1 if l > 0 else n + abs(l) - 1] = 1
        pre.append([0] * P)
        post.append(b)
    return pre, post, [1] * P, P, len(pre)


def lean_rows(n, clauses):
    K = len(clauses)
    rows = []
    for c in range(n + K):
        pre = [int(c < n and (q == c or q == n + c)) for q in range(2 * n)]
        post = []
        for q in range(2 * n):
            if c < n:
                post.append(0)
            else:
                cl = clauses[c - n]
                post.append(int((q + 1) in cl) if q < n else int(-(q - n + 1) in cl))
        rows.append((tuple(pre), tuple(post)))
    return sorted(rows)


def population(trials=150, seed=17):
    pool = [(2, [list(c) for c in cnf]) for m in range(1, 4)
            for cnf in combinations_with_replacement(all_clauses(2, 2), m)]
    rng = random.Random(seed)
    for _ in range(trials):
        n = rng.randint(2, 3)
        pool.append((n, random_cnf(rng, n, rng.randint(1, 6 * n), rng.choice([2, 3]))))
    return pool


def run(trials=150):
    agree = disagree = sat = unsat = shape_bad = bridge_bad = abl = cf_wrong = 0
    for n, cnf in population(trials):
        pre, post, cap, P, T = il_net(n, cnf)
        shape_bad += conflict_places(pre, P, T) != 0 or \
            all(any(r) for r in pre)
        bridge_bad += sorted(zip(map(tuple, pre), map(tuple, post))) != lean_rows(n, cnf)
        v, _ = preserves(pre, post, cap, P, T)
        s = satisfiable(n, cnf)
        sat += s
        unsat += not s
        agree += v == (not s)
        disagree += v != (not s)
        va, _ = preserves(*il_net(n, cnf, drop_var=True))
        abl += va != (not s)
        cf_wrong += cf_decide(pre, post, cap, P, T) != (not s)
    empty_v, _ = preserves(*il_net(2, []))
    gates = {
        "reduction_is_exact": disagree == 0 and agree > 0,
        "both_outcomes_occur": sat > 0 and unsat > 0,
        "every_net_conflict_free_with_inputless_transition": shape_bad == 0,
        "bridge_matches_lean": bridge_bad == 0,
        "ablation_drop_variable_transitions_breaks": abl > 0,
        "conflict_free_procedure_wrong_outside_its_hypothesis": cf_wrong > 0,
        "empty_cnf_exception_as_stated": empty_v is True and satisfiable(2, []),
    }
    return {"schema": "cbmd.petri-inputless-hardness.v1",
            "formulas": agree + disagree, "agree": agree, "disagree": disagree,
            "satisfiable": sat, "unsatisfiable": unsat, "shape_failures": shape_bad,
            "bridge_mismatches": bridge_bad, "ablation_wrong": abl,
            "conflict_free_procedure_wrong": cf_wrong, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["the reduction's correctness is compiled; coNP membership and polynomial running time are written arguments",
                          "input-less transitions are a modelling choice this dossier otherwise excludes; the point is that the exclusion is load-bearing"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 150)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
