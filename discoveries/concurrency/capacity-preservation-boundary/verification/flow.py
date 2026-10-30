"""The draining regime: a characterization where the all-full obstruction stops.

Revision 0.2.0 proved that a net in which every transition increases some place
preserves exactly when it cannot fire at all, and left the **draining** case
open -- transitions that consume without producing, which keep the all-full
marking alive and are exactly what an absorbing sink supplies.

This settles it for the unit-weight flow family: each transition takes one token
from a place and either moves it to another place or discards it.  Say a set `S`
of places is an OBSTRUCTION when

  1. every member has positive capacity,
  2. no drain takes from a member -- a drain is never blocked, so a member
     feeding one could always fire,
  3. every mover out of a member lands in `S` or in a zero-capacity place --
     the two ways a mover can be blocked,
  4. some mover takes from a member, or nothing is enabled and there is no
     deadlock to invent.

Then `PRESERVES <=> no obstruction exists`, proved in
`verification/lean/CBMDPetriCapacity/Flow.lean`.

Condition 4 is not decoration.  Without it the predicate is sound but
INCOMPLETE, because a set of full places that no transition draws from blocks
nothing; the first draft of this script omitted it and the incompleteness count
is kept as a recorded control below.

Three things are measured, since a proof is only worth its statement:

  * the characterization against the exact semantics of `petri.py` -- the
    dossier's own model, reused rather than reimplemented, so the flow family
    is encoded into pre/post matrices and handed to it;
  * the greatest-fixpoint decision procedure against the literal existential
    form that Lean proves, by brute force over all subsets of places;
  * condition 4 ablated, which must produce incompleteness and no unsoundness.
"""
from __future__ import annotations

import json
import os
import sys
from itertools import combinations_with_replacement, product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from petri import preserves as exact_preserves


# ------------------------------------------------------------ the family
def transitions_for(P):
    """('m', a, b) moves one token a -> b;  ('d', a) discards one from a."""
    return ([("m", a, b) for a in range(P) for b in range(P) if a != b]
            + [("d", a) for a in range(P)])


def matrices(trs, P):
    """Encode a flow net as the pre/post matrices `petri.py` consumes."""
    T = len(trs)
    pre = [[0] * P for _ in range(T)]
    post = [[0] * P for _ in range(T)]
    for t, tr in enumerate(trs):
        pre[t][tr[1]] = 1
        if tr[0] == "m":
            post[t][tr[2]] = 1
    return pre, post


# --------------------------------------------------- the characterization
def is_obstruction(S, trs, cap, require_fires=True, drop=()):
    """`drop` names conditions to ignore, for the ablation control."""
    if not S:
        return False
    if 1 not in drop and any(cap[q] < 1 for q in S):
        return False
    if 2 not in drop and any(tr[0] == "d" and tr[1] in S for tr in trs):
        return False
    if 3 not in drop:
        for tr in trs:
            if tr[0] == "m" and tr[1] in S and not (tr[2] in S or cap[tr[2]] == 0):
                return False
    if require_fires and not any(tr[0] == "m" and tr[1] in S for tr in trs):
        return False
    return True


def greatest_fixpoint(trs, cap, P):
    """Peel places that cannot belong to any obstruction.  Every obstruction is
    contained in what is left, so testing the remainder is enough."""
    drains = {tr[1] for tr in trs if tr[0] == "d"}
    S = {q for q in range(P) if cap[q] >= 1 and q not in drains}
    changed = True
    while changed:
        changed = False
        for u in list(S):
            for tr in trs:
                if tr[0] == "m" and tr[1] == u and not (tr[2] in S or cap[tr[2]] == 0):
                    S.discard(u)
                    changed = True
                    break
    return S


def predicted_preserves(trs, cap, P, require_fires=True):
    S = greatest_fixpoint(trs, cap, P)
    return not is_obstruction(S, trs, cap, require_fires)


def exists_obstruction_bruteforce(trs, cap, P, drop=()):
    for bits in range(1, 1 << P):
        S = {q for q in range(P) if bits >> q & 1}
        if is_obstruction(S, trs, cap, drop=drop):
            return True
    return False


# ----------------------------------------------------------------- census
def census(P, T, capmax):
    opts = transitions_for(P)
    row = {"box": {"places": P, "transitions": T, "max_capacity": capmax},
           "systems": 0, "preserving": 0, "not_preserving": 0,
           "UNSOUND": 0, "INCOMPLETE": 0, "samples": [],
           "fixpoint_disagrees_with_existential": 0,
           "without_condition_4": {"UNSOUND": 0, "INCOMPLETE": 0},
           "ablation": {k: {"UNSOUND": 0, "INCOMPLETE": 0} for k in (1, 2, 3)}}
    for trs in combinations_with_replacement(opts, T):
        pre, post = matrices(trs, P)
        for cap in product(range(capmax + 1), repeat=P):
            row["systems"] += 1
            ok, _witness = exact_preserves(pre, post, list(cap), P, T)
            if ok is None:
                continue
            row["preserving" if ok else "not_preserving"] += 1

            pred = predicted_preserves(trs, cap, P)
            if pred and not ok:
                row["UNSOUND"] += 1
                if len(row["samples"]) < 4:
                    row["samples"].append({"transitions": [list(x) for x in trs],
                                           "capacity": list(cap), "kind": "unsound"})
            elif ok and not pred:
                row["INCOMPLETE"] += 1
                if len(row["samples"]) < 4:
                    row["samples"].append({"transitions": [list(x) for x in trs],
                                           "capacity": list(cap), "kind": "incomplete"})

            # the decision procedure against the statement Lean proves
            if (not pred) != exists_obstruction_bruteforce(trs, cap, P):
                row["fixpoint_disagrees_with_existential"] += 1

            # conditions 1-3 ablated, decided by brute force since dropping a
            # condition invalidates the peeling argument behind the fixpoint
            for k in (1, 2, 3):
                p_k = not exists_obstruction_bruteforce(trs, cap, P, drop=(k,))
                if p_k and not ok:
                    row["ablation"][k]["UNSOUND"] += 1
                elif ok and not p_k:
                    row["ablation"][k]["INCOMPLETE"] += 1

            # condition 4 ablated
            pred4 = predicted_preserves(trs, cap, P, require_fires=False)
            if pred4 and not ok:
                row["without_condition_4"]["UNSOUND"] += 1
            elif ok and not pred4:
                row["without_condition_4"]["INCOMPLETE"] += 1
    return row


def run(boxes=((3, 3, 1), (3, 3, 2), (4, 4, 1), (4, 3, 2))):
    rows = [census(*b) for b in boxes]
    tot = lambda k: sum(r[k] for r in rows)                       # noqa: E731
    ab_inc = sum(r["without_condition_4"]["INCOMPLETE"] for r in rows)
    ab_uns = sum(r["without_condition_4"]["UNSOUND"] for r in rows)
    ab123 = {k: {"UNSOUND": sum(r["ablation"][str(k)]["UNSOUND"] if str(k) in r["ablation"]
                                else r["ablation"][k]["UNSOUND"] for r in rows),
                 "INCOMPLETE": sum(r["ablation"][str(k)]["INCOMPLETE"] if str(k) in r["ablation"]
                                   else r["ablation"][k]["INCOMPLETE"] for r in rows)}
             for k in (1, 2, 3)}
    gates = {
        "characterization_is_exact": tot("UNSOUND") == 0 and tot("INCOMPLETE") == 0,
        "both_outcomes_occur": tot("preserving") > 0 and tot("not_preserving") > 0,
        "fixpoint_matches_the_proved_existential": tot("fixpoint_disagrees_with_existential") == 0,
        "condition_4_is_load_bearing": ab_inc > 0,
        "conditions_1_to_3_are_load_bearing":
            all(ab123[k]["UNSOUND"] + ab123[k]["INCOMPLETE"] > 0 for k in (1, 2, 3)),
        "condition_4_ablation_stays_sound": ab_uns == 0,
    }
    return {"schema": "cbmd.petri-flow-characterization.v1",
            "censuses": rows,
            "totals": {"systems": tot("systems"),
                       "preserving": tot("preserving"),
                       "not_preserving": tot("not_preserving"),
                       "unsound": tot("UNSOUND"),
                       "incomplete": tot("INCOMPLETE"),
                       "fixpoint_disagrees_with_existential":
                           tot("fixpoint_disagrees_with_existential"),
                       "conditions_1_to_3_ablated": ab123,
                       "condition_4_ablated_incomplete": ab_inc,
                       "condition_4_ablated_unsound": ab_uns},
            "gates": gates,
            "pass": all(gates.values()),
            "nonclaims": [
                "the characterization is proved in verification/lean/; this census "
                "corroborates it and is not the proof",
                "unit arc weights only; nothing here covers weighted flow",
                "the greatest fixpoint is how the condition is decided on a finite net; "
                "the proved statement is the existential one",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    result = run()
    print(json.dumps(result, indent=1))
    raise SystemExit(0 if result["pass"] else 1)
