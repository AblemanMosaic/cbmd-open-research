"""The all-full obstruction, and the necessity of its hypothesis.

Version 0.1.0 of this dossier mapped the boundary by census.  This checks a
statement that is now proved in `verification/lean/`:

    If every transition strictly increases the count at some place, then
        PRESERVES(N, C)  <=>  no transition can ever fire inside the box
                         <=>  for every t there is a q with C(q) < pre(t, q)

The witness for the forward direction is the all-full marking C itself.  Firing
any transition from it would push its strictly-increasing place over capacity,
so C is capacity-dead; and any transition whose inputs fit inside the capacities
is ordinarily enabled there.  So such a net is either completely inert or has a
capacity-invented deadlock, with no third case, and enlarging the capacities
cannot help because the witness is built from the capacities.

Two populations are measured, because the theorem is only interesting if both
are non-empty:

  * INSIDE the class: the predicted equivalence must hold with no exception.
    The count of NON-INERT members matters -- those are the nets the theorem
    claims all fail, and if there were none the agreement would be vacuous.
  * OUTSIDE the class: nets with a non-increasing transition (a drain) on which
    the conclusion would be WRONG.  If that count were zero, the hypothesis
    would be idle and the theorem should be stated without it.
"""
from __future__ import annotations

import json
import os
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from petri import nets, preserves  # the exact semantics of version 0.1.0


def increasing(pre, post, P, T):
    return all(any(post[t][q] > pre[t][q] for q in range(P)) for t in range(T))


def inert(pre, cap, P, T):
    return all(any(cap[q] < pre[t][q] for q in range(P)) for t in range(T))


def census(P, T, maxw, capmax):
    inside = {"members": 0, "agree": 0, "DISAGREE": 0, "non_inert_members": 0,
              "samples": []}
    outside = {"members": 0, "conclusion_would_be_wrong_on": 0, "samples": []}
    skipped = 0
    for pre, post in nets(P, T, maxw):
        for cap in product(range(capmax + 1), repeat=P):
            # petri.preserves returns (verdict, witness), not a bare bool;
            # comparing the pair to a bool silently makes every case disagree.
            ok, _witness = preserves(pre, post, list(cap), P, T)
            if ok is None:
                skipped += 1
                continue
            pred = inert(pre, cap, P, T)
            if increasing(pre, post, P, T):
                inside["members"] += 1
                if not pred:
                    inside["non_inert_members"] += 1
                if ok == pred:
                    inside["agree"] += 1
                else:
                    inside["DISAGREE"] += 1
                    if len(inside["samples"]) < 4:
                        inside["samples"].append(
                            {"pre": pre, "post": post, "capacity": list(cap),
                             "preserves": ok, "predicted": pred})
            else:
                outside["members"] += 1
                if ok != pred:
                    outside["conclusion_would_be_wrong_on"] += 1
                    if len(outside["samples"]) < 3:
                        outside["samples"].append(
                            {"pre": pre, "post": post, "capacity": list(cap),
                             "preserves": ok, "inert": pred})
    return {"box": {"places": P, "transitions": T, "max_arc_weight": maxw,
                    "max_capacity": capmax},
            "inside_the_class": inside, "outside_the_class": outside,
            "skipped": skipped}


def run(boxes=((2, 2, 2, 2), (3, 2, 1, 2), (2, 3, 1, 2))):
    rows = [census(*b) for b in boxes]
    total_in = sum(r["inside_the_class"]["members"] for r in rows)
    disagree = sum(r["inside_the_class"]["DISAGREE"] for r in rows)
    non_inert = sum(r["inside_the_class"]["non_inert_members"] for r in rows)
    wrong_outside = sum(r["outside_the_class"]["conclusion_would_be_wrong_on"]
                        for r in rows)
    gates = {
        "equivalence_holds_inside_the_class": disagree == 0,
        "class_is_populated": total_in > 0,
        "class_contains_non_inert_nets": non_inert > 0,
        "hypothesis_is_load_bearing": wrong_outside > 0,
    }
    return {"schema": "cbmd.petri-allfull-obstruction.v1",
            "censuses": rows,
            "totals": {"inside_the_class": total_in,
                       "disagreements": disagree,
                       "non_inert_members": non_inert,
                       "outside_where_conclusion_would_be_wrong": wrong_outside},
            "gates": gates,
            "pass": all(gates.values()),
            "nonclaims": [
                "finite censuses over stated boxes; the unbounded statement is the "
                "Lean theorem, not this script",
                "agreement inside the class is corroboration of a proof, not the proof",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    result = run()
    print(json.dumps(result, indent=1))
    raise SystemExit(0 if result["pass"] else 1)
