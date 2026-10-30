"""Free choice does not help (revision 0.10.0).

The hardness of revision 0.4.0 survives in STRICT FREE-CHOICE nets -- a place
with several output transitions is the only input place of each -- with unit
weights, every capacity 1, and one or two input places per transition.  Lean:
`FreeChoice.lean`, `fc_preserves_iff_unsatisfiable`, `free_choice`,
`input_places`.

Construction for a CNF on n variables: places x_i, xbar_i, g (capacity 1);
transitions
    E_i : x_i, xbar_i -> (nothing)          blocked iff not both hold
    H_i : g -> x_i, xbar_i                  blocked iff g empty or x_i or xbar_i
    C_k : g -> literal places of clause k   blocked iff g empty or a literal holds

Gates (each required):
  * exact: the net preserves iff the CNF is unsatisfiable, judged by this
    dossier's own `petri.preserves` against a brute-force SAT oracle;
  * both outcomes occur;
  * every net is strict free-choice, checked structurally;
  * input places per transition in [1, 2];
  * CONTROL: the free-choice checker rejects the revision 0.4.0 nets, which
    are not free choice -- otherwise the free-choice gate would be idle;
  * BRIDGE: the net equals a literal transcription of the Lean `fpre`/`fpost`
    (transitions as a multiset);
  * ABLATION E: dropping the E family must break exactness -- it is the only
    multi-input family, so without it the net is single-input and polynomial;
  * ABLATION H: dropping the H family may break exactness ONLY on the empty
    CNF.  This is a prediction of the Lean proof, whose backward direction
    never uses H and whose forward direction needs it only to have a
    g-transition when there are no clauses.
"""
from __future__ import annotations

import json
import os
import random
import sys
from itertools import combinations_with_replacement

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from petri import preserves  # noqa: E402
from hardness import all_clauses, build, guarded_cnf, random_cnf, satisfiable  # noqa: E402


def fc_net(n, clauses, drop=None):
    P = 2 * n + 1
    g = 2 * n
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
        if drop != "E":
            t([i, n + i], [])
        if drop != "H":
            t([g], [i, n + i])
    for cl in clauses:
        t([g], [abs(l) - 1 if l > 0 else n + abs(l) - 1 for l in cl])
    return pre, post, [1] * P, P, len(pre)


def lean_rows(n, clauses):
    """Literal transcription of FreeChoice.fpre / fpost."""
    K = len(clauses)
    neg = [[False] * n for _ in clauses]
    pos = [[False] * n for _ in clauses]
    for k, cl in enumerate(clauses):
        for l in cl:
            (pos if l > 0 else neg)[k][abs(l) - 1] = True
    A = n + n + 1
    rows = []
    for c in range(n + n + K):
        pre = [int((q == c or q == n + c) if c < n else q == n + n) for q in range(A)]
        post = []
        for q in range(A):
            if c < n:
                v = 0
            elif c < n + n:
                v = int(q == c - n or q == n + (c - n))
            else:
                k = c - (n + n)
                v = int(pos[k][q]) if q < n else int(neg[k][q - n]) if q < n + n else 0
            post.append(v)
        rows.append((tuple(pre), tuple(post)))
    return sorted(rows)


def strict_free_choice(pre, P, T):
    for q in range(P):
        outs = [t for t in range(T) if pre[t][q] > 0]
        if len(outs) > 1 and any(sum(1 for r in range(P) if pre[t][r] > 0) != 1 for t in outs):
            return False
    return True


def population(trials=150, seed=7):
    pool = [(2, [list(c) for c in cnf]) for m in range(0, 4)
            for cnf in combinations_with_replacement(all_clauses(2, 2), m)]
    rng = random.Random(seed)
    for _ in range(trials):
        n = rng.randint(2, 3)
        pool.append((n, random_cnf(rng, n, rng.randint(1, 6 * n), rng.choice([2, 3]))))
    return pool


def run(trials=150):
    agree = disagree = sat = unsat = nonfc = bridge_bad = 0
    lo, hi = 99, 0
    abl_e = abl_h = abl_h_nonempty = 0
    samples = []
    for n, cnf in population(trials):
        pre, post, cap, P, T = fc_net(n, cnf)
        nonfc += not strict_free_choice(pre, P, T)
        counts = [sum(1 for q in range(P) if r[q]) for r in pre]
        lo, hi = min(lo, min(counts)), max(hi, max(counts))
        bridge_bad += sorted(zip(map(tuple, pre), map(tuple, post))) != lean_rows(n, cnf)
        verdict, _ = preserves(pre, post, cap, P, T)
        s = satisfiable(n, cnf)
        sat += s
        unsat += not s
        if verdict == (not s):
            agree += 1
        else:
            disagree += 1
            if len(samples) < 3:
                samples.append({"n": n, "clauses": cnf})
        ve, _ = preserves(*fc_net(n, cnf, "E"))
        abl_e += ve != (not s)
        vh, _ = preserves(*fc_net(n, cnf, "H"))
        if vh != (not s):
            abl_h += 1
            abl_h_nonempty += len(cnf) > 0
    # Control on the free-choice checker itself: the 0.4.0 nets are not free
    # choice (clause transitions share atoms with different input sets), and
    # the checker must say so, or the free-choice gate is idle.
    rejected = 0
    for n, cnf in population(trials):
        p0, _q0, _c0, P0, T0 = build(*guarded_cnf(n, cnf))
        rejected += not strict_free_choice(p0, P0, T0)
    gates = {
        "free_choice_check_rejects_0_4_0_nets": rejected > 0,
        "reduction_is_exact": disagree == 0 and agree > 0,
        "both_outcomes_occur": sat > 0 and unsat > 0,
        "every_net_strict_free_choice": nonfc == 0,
        "one_or_two_input_places": lo >= 1 and hi <= 2,
        "bridge_matches_lean": bridge_bad == 0,
        "ablation_E_breaks": abl_e > 0,
        "ablation_H_breaks_only_empty_cnf": abl_h_nonempty == 0,
    }
    return {"schema": "cbmd.petri-free-choice-hardness.v1",
            "formulas": agree + disagree, "agree": agree, "disagree": disagree,
            "satisfiable": sat, "unsatisfiable": unsat,
            "input_places_per_transition": {"min": lo, "max": hi},
            "not_free_choice": nonfc, "revision_0_4_0_nets_rejected": rejected, "bridge_mismatches": bridge_bad,
            "ablation_E_wrong": abl_e, "ablation_H_wrong": abl_h,
            "ablation_H_wrong_on_nonempty_cnf": abl_h_nonempty,
            "samples": samples, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": [
                "the reduction's correctness is compiled; coNP membership and the reduction's polynomial running time are written arguments, as in revision 0.4.0",
                "related but distinct: deadlock (a reachable dead marking) is NP-complete for free-choice nets (Cheng, Esparza, Palsberg); this problem quantifies over admissible markings, not reachable ones",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 150)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
