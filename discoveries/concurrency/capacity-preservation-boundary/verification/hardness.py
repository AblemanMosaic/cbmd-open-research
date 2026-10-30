"""Deciding capacity-preservation is coNP-hard, at exactly two input places.

Revision 0.3.0 characterizes preservation for unit-weight nets whose
transitions have ONE input place, by a greatest fixpoint computable in
polynomial time.  Revision 0.1.0 found by census that the characterization
breaks as soon as a transition has two input places, and left open whether some
other local condition repairs it.  This answers that in the strongest available
form: with two input places the problem is coNP-hard, so no polynomial-time
condition of any kind is exact unless P = NP.

## How a transition fails to be capacity enabled

    t is NOT capacity enabled  <=>  (some q has m(q) < pre(t,q))        ... (A)
                                 or (some q has m(q)-pre+post > C(q))   ... (B)

With unit weights and capacities in {0,1}:
  * (A) with pre(t,q) = 1 reads "q is FALSE" -- a negative literal, and an
    input place;
  * (B) with pre(t,q) = 0, post(t,q) = 1, C(q) = 1 reads "q is TRUE" -- a
    positive literal, and no input place.

So one transition per clause -- inputs on the negative literals, outputs on the
positive ones -- is blocked exactly when its clause is satisfied.  The number of
input places is the number of negative literals.

## Keeping every transition fed

A transition with no input place is a modelling oddity, and the census
generator of this dossier excludes them, so the reduction should not rely on
them.  That forces every clause to carry at least one negative literal -- and
such a CNF is always satisfied by setting everything false.  The reduction
therefore targets the right question:

    given a CNF in which every clause has at least one negative literal,
    is there a model that is not all-false?

which the "ordinarily enabled somewhere" half of a bad marking expresses: add,
for each variable place a, a transition consuming from a and producing into a
place of capacity 0.  It is blocked always and ordinarily enabled exactly when
a holds a token.

That problem is NP-hard.  Given an arbitrary CNF over x_1..x_n, introduce
xbar_i and a guard g, and take

    (NOT x_i OR NOT xbar_i)             -- 2 negative literals
    (x_i OR xbar_i OR NOT g)            -- 1
    (NOT x_i OR g), (NOT xbar_i OR g)   -- 1
    each original clause, with x_i kept and NOT x_i rewritten as xbar_i,
                            then OR NOT g   -- 1

Any model that is not all-false has g true: if g is false then every x_i and
xbar_i is false by the guard clauses.  With g true the first two families make
each pair exactly one-hot, which is a total assignment, and the rewritten
clauses say it satisfies the original.  Conversely a satisfying assignment
gives such a model.  No clause has more than two negative literals, so no
transition has more than two input places, and none has fewer than one.

## What is and is not claimed

The complement -- does a bad marking exist -- is in NP: a marking is
polynomial-sized and both halves of "bad" are checkable in O(PT).  So
preservation is coNP-complete.  That is a written argument.  What is machine
checked here is the REDUCTION: that the constructed net preserves exactly when
the input CNF is unsatisfiable, against a brute-force oracle.
"""
from __future__ import annotations

import json
import random
import os
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from petri import preserves as exact_preserves


def preserves(pre, post, cap, P, T):
    """This dossier's own semantics, reused rather than reimplemented; it
    returns a (verdict, witness) pair."""
    verdict, _witness = exact_preserves(pre, post, cap, P, T)
    return verdict


# ------------------------------------------------------------ the encoding
def guarded_cnf(n, clauses):
    """x_i -> atom i, xbar_i -> atom n+i, g -> atom 2n+1 (1-based literals)."""
    def x(i): return i
    def xb(i): return n + i
    g = 2 * n + 1
    out = []
    for i in range(1, n + 1):
        out.append([-x(i), -xb(i)])
        out.append([x(i), xb(i), -g])
        out.append([-x(i), g])
        out.append([-xb(i), g])
    for cl in clauses:
        out.append([x(l) if l > 0 else xb(-l) for l in cl] + [-g])
    return 2 * n + 1, out


def build(n_atoms, clauses):
    """Places 0..n_atoms-1 are atoms (capacity 1); the last place is a sink of
    capacity 0.  One transition per clause, plus one per atom to supply the
    'ordinarily enabled' half."""
    P = n_atoms + 1
    sink = n_atoms
    cap = [1] * n_atoms + [0]
    pre, post = [], []
    for cl in clauses:
        a = [0] * P
        b = [0] * P
        for lit in cl:
            v = abs(lit) - 1
            if lit > 0:
                b[v] = 1                      # blocked when the atom is true
            else:
                a[v] = 1                      # blocked when the atom is false
        pre.append(a)
        post.append(b)
    for v in range(n_atoms):                  # always blocked, enabled iff atom true
        a = [0] * P
        b = [0] * P
        a[v] = 1
        b[sink] = 1
        pre.append(a)
        post.append(b)
    return pre, post, cap, P, len(pre)


def input_place_counts(pre, P):
    return [sum(1 for q in range(P) if row[q] > 0) for row in pre]


def satisfiable(n, clauses):
    for bits in product([0, 1], repeat=n):
        if all(any((bits[abs(l) - 1] == 1) if l > 0 else (bits[abs(l) - 1] == 0)
                   for l in cl) for cl in clauses):
            return True
    return False


def random_cnf(rng, n, m, k):
    return [[v if rng.random() < 0.5 else -v
             for v in rng.sample(range(1, n + 1), min(k, n))] for _ in range(m)]


def run(trials=240, seed=1030):
    rng = random.Random(seed)
    agree = disagree = sat = unsat = 0
    lo, hi = 99, 0
    samples = []
    for _ in range(trials):
        n = rng.randint(2, 3)
        mode = rng.randint(0, 1)
        clauses = random_cnf(rng, n, rng.randint(1, 3) if mode == 0
                             else rng.randint(3 * n, 6 * n), rng.choice([2, 3]))
        n_atoms, enc = guarded_cnf(n, clauses)
        pre, post, cap, P, T = build(n_atoms, enc)
        counts = input_place_counts(pre, P)
        lo, hi = min(lo, min(counts)), max(hi, max(counts))
        ok = preserves(pre, post, cap, P, T)
        if ok is None:
            continue
        s = satisfiable(n, clauses)
        sat += s
        unsat += (not s)
        if ok == (not s):
            agree += 1
        else:
            disagree += 1
            if len(samples) < 4:
                samples.append({"clauses": clauses, "preserves": ok, "satisfiable": s})
    gates = {
        "reduction_is_exact": disagree == 0,
        "both_outcomes_occur": sat > 0 and unsat > 0,
        "every_transition_has_an_input_place": lo >= 1,
        "at_most_two_input_places": hi <= 2,
    }
    return {"schema": "cbmd.petri-preservation-hardness.v2",
            "trials": trials, "agree": agree, "DISAGREE": disagree,
            "satisfiable_instances": sat, "unsatisfiable_instances": unsat,
            "input_places_per_transition": {"min": lo, "max": hi},
            "samples": samples, "gates": gates, "pass": all(gates.values()),
            "nonclaims": [
                "the complexity statement is a written argument; what is machine "
                "checked here is the correctness of the reduction",
                "unit arc weights and capacities in {0,1} only -- which makes the "
                "hardness stronger, not weaker",
                "the exhaustive pass enumerates every CNF in a small box; the random "
                "pass reaches larger instances. Neither proves the reduction, which is "
                "the written argument",
            ],
            "authority_effect": "NONE"}


def all_clauses(n, max_width=3):
    """Every clause over n variables, up to the given width, no repeated
    variable inside a clause."""
    from itertools import combinations
    out = []
    for w in range(1, min(max_width, n) + 1):
        for vs in combinations(range(1, n + 1), w):
            for signs in product([1, -1], repeat=w):
                out.append([s * v for s, v in zip(signs, vs)])
    return out


def exhaustive(n=2, max_clauses=3, max_width=2):
    """Every CNF over n variables with at most max_clauses clauses, rather than
    a random sample.  A reduction is a claim about ALL inputs, so a census that
    enumerates them is worth more than one that draws from them -- in
    particular it cannot miss a shape the sampler never produced."""
    from itertools import combinations_with_replacement
    clauses_all = all_clauses(n, max_width)
    agree = disagree = sat = unsat = 0
    lo, hi = 99, 0
    samples = []
    for m in range(1, max_clauses + 1):
        for cnf in combinations_with_replacement(clauses_all, m):
            cnf = [list(c) for c in cnf]
            n_atoms, enc = guarded_cnf(n, cnf)
            pre, post, cap, P, T = build(n_atoms, enc)
            counts = input_place_counts(pre, P)
            lo, hi = min(lo, min(counts)), max(hi, max(counts))
            ok = preserves(pre, post, cap, P, T)
            if ok is None:
                continue
            s_ = satisfiable(n, cnf)
            sat += s_
            unsat += (not s_)
            if ok == (not s_):
                agree += 1
            else:
                disagree += 1
                if len(samples) < 4:
                    samples.append({"clauses": cnf, "preserves": ok,
                                    "satisfiable": s_})
    return {"box": {"variables": n, "max_clauses": max_clauses,
                    "max_clause_width": max_width,
                    "distinct_clauses": len(clauses_all)},
            "formulas": agree + disagree,
            "agree": agree, "DISAGREE": disagree,
            "satisfiable": sat, "unsatisfiable": unsat,
            "input_places_per_transition": {"min": lo, "max": hi},
            "samples": samples,
            "gates": {"exhaustive_reduction_is_exact": disagree == 0,
                      "both_outcomes_occur": sat > 0 and unsat > 0,
                      "every_transition_has_an_input_place": lo >= 1,
                      "at_most_two_input_places": hi <= 2}}


if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 240
    r = run(trials=trials)
    r["exhaustive"] = exhaustive()
    r["gates"].update(r["exhaustive"]["gates"])
    r["pass"] = all(r["gates"].values())
    print(json.dumps(r, indent=1))
    raise SystemExit(0 if r["pass"] else 1)
