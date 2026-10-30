"""Does the Lean well-foundedness reformulation say what the census measured?

Revision 0.5.0 replaces the rank hypotheses of the characterization by

    WellFounded (LiveArc)   where   LiveArc v u  <->  Live u /\\ Live v /\\ m(u,v) > 0

and proves

    (A) wf_terminal_implies_ordinary_stable
        WF /\\ live_closed /\\ live_bound /\\ capacity-terminal  ->  ordinarily stable
    (B) wellFounded_iff_no_filled_set
        under live_closed:   WF  <->  no FilledSet exists

A Lean proof is only as interesting as the statement it proves, so this script
checks the STATEMENTS against the exhaustive population, independently of the
census predicate in characterize.py:

  * WF is decided by Kahn peeling (repeatedly delete live vertices with no
    live out-arc), not by the DFS colouring that characterize.py uses;
  * FilledSet existence is decided by a greatest-fixpoint kernel, which has no
    counterpart in characterize.py at all;
  * the conclusion of (A) is simulated directly -- every capacity-reachable
    capacity-terminal state is tested for ordinary stability.  That is the
    theorem's own conclusion, which is weaker than TRANSFER; checking TRANSFER
    instead would not test what Lean proves.

Content gates (not hash gates).  A pass requires, in addition to 0 unsound:

  * the WF x conclusion table shows WF alone is NOT sufficient (wf_noconcl > 0),
    so live_closed and live_bound are not idle passengers;
  * it also shows WF is NECESSARY (nowf_concl = 0) on a non-empty failure
    population.  That cell being empty is a prediction of 0.5.0 --
    filled_set_obstruction composed with filledSetOfNotWellFounded -- so an
    occupied cell would refute the revision rather than merely weaken it;
  * (B) agrees in BOTH directions on the live_closed sub-population, AND
    disagrees somewhere outside it -- otherwise live_closed would be an idle
    hypothesis and the equivalence would be weaker than stated;
  * the greedy kernel actually finds FilledSets;
  * each hypothesis of (A), replaced by `True` in turn, produces unsoundness.
    A hypothesis whose removal changes nothing was never doing any work, and a
    0-unsound headline for the conjunction would then be evidence of nothing.
"""
from __future__ import annotations

import json
import os
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from characterize import cap_terminals, digraphs, live, od  # noqa: E402


# ---------------------------------------------------------------- hypotheses
def well_founded(a, n, L):
    """WellFounded LiveArc, by peeling.  A finite relation is well founded iff
    repeatedly deleting elements with no predecessor in the relation empties it.
    `LiveArc v u` holds when u sends to v, so the elements to peel are the live
    vertices with no live out-arc."""
    remaining = set(L)
    changed = True
    while changed:
        changed = False
        for u in list(remaining):
            if not any(a[u][v] > 0 for v in remaining):
                remaining.discard(u)
                changed = True
    return not remaining


def live_closed(a, n, L):
    return all(a[u][v] == 0 for u in L for v in range(n) if v not in L)


def live_bound(a, s, c, L):
    """Lean's per-arc form: od v + m(u,v) <= C v + 1 for live u -> live v."""
    for u in L:
        for v in L:
            if a[u][v] > 0 and od(a, s, v) + a[u][v] > c[v] + 1:
                return False
    return True


def has_filled_set(a, n, L):
    """Greatest S such that every live v in S has a positive arc into S, with a
    live witness.  Dead vertices are never removed: they carry no obligation in
    the FilledSet structure.  Returns (exists, S)."""
    S = set(range(n))
    changed = True
    while changed:
        changed = False
        for v in list(S):
            if v in L and not any(a[v][w] > 0 for w in S):
                S.discard(v)
                changed = True
    return any(v in S for v in L), S


# ---------------------------------------------------------------- conclusion
def ordinarily_stable(a, s, n, y):
    return all(y[u] < od(a, s, u) for u in range(n))


def every_terminal_is_stable(a, s, c, n):
    """The conclusion of wf_terminal_implies_ordinary_stable, over every
    admissible initial state.  None if the search was cut off."""
    for x in product(*(range(ci + 1) for ci in c)):
        terms = cap_terminals(a, s, tuple(c), n, x)
        if terms is None:
            return None
        for y in terms:
            if not ordinarily_stable(a, s, n, y):
                return False
    return True


# ---------------------------------------------------------------------- run
def run(n_max=3, mm=2, ms=1, slack=2):
    out = {"schema": "cbmd.wellfounded-equivalence.v1",
           "box": {"n_max": n_max, "max_multiplicity": mm,
                   "max_sink_multiplicity": ms,
                   "capacity_range": f"0..d(v)+{slack}"}}

    # theorem (A): hypotheses -> conclusion
    unsound_A = []                       # hypotheses hold, conclusion fails
    table = {"wf_concl": 0, "wf_noconcl": 0, "nowf_concl": 0, "nowf_noconcl": 0}
    hyp_hold = 0
    skipped = 0

    # theorem (B): WF <-> no FilledSet, under live_closed
    b_agree = b_disagree = 0
    b_disagree_sample = []
    nolc_agree = nolc_disagree = 0       # must be > 0 disagreements, or live_closed is idle
    nolc_sample = []
    filled_found = 0

    for n in range(1, n_max + 1):
        for a, s in digraphs(n, mm, ms):
            for c in product(*(range(od(a, s, v) + slack + 1) for v in range(n))):
                c = tuple(c)
                L = live(a, s, c, n)
                wf = well_founded(a, n, L)
                lc = live_closed(a, n, L)
                lb = live_bound(a, s, c, L)
                fs, _ = has_filled_set(a, n, L)
                if fs:
                    filled_found += 1

                # ---- theorem (B)
                if lc:
                    if wf == (not fs):
                        b_agree += 1
                    else:
                        b_disagree += 1
                        if len(b_disagree_sample) < 6:
                            b_disagree_sample.append(
                                {"arcs": [list(r) for r in a], "sink": list(s),
                                 "capacity": list(c), "live": L,
                                 "wf": wf, "filled_set": fs})
                else:
                    if wf == (not fs):
                        nolc_agree += 1
                    else:
                        nolc_disagree += 1
                        if len(nolc_sample) < 3:
                            nolc_sample.append(
                                {"arcs": [list(r) for r in a], "sink": list(s),
                                 "capacity": list(c), "live": L,
                                 "wf": wf, "filled_set": fs})

                # ---- theorem (A)
                concl = every_terminal_is_stable(a, s, c, n)
                if concl is None:
                    skipped += 1
                    continue
                key = ("wf_" if wf else "nowf_") + ("concl" if concl else "noconcl")
                table[key] += 1
                if wf and lc and lb:
                    hyp_hold += 1
                    if not concl:
                        if len(unsound_A) < 6:
                            unsound_A.append(
                                {"arcs": [list(r) for r in a], "sink": list(s),
                                 "capacity": list(c), "live": L})

    conclusion_holds = table["wf_concl"] + table["nowf_concl"]
    out["theorem_A"] = {
        "hypotheses_satisfied": hyp_hold,
        "conclusion_holds": conclusion_holds,
        "UNSOUND": len(unsound_A),
        "INCOMPLETE": conclusion_holds - (hyp_hold - len(unsound_A)),
        "unsound_samples": unsound_A,
        "wf_by_conclusion_table": table,
        "skipped": skipped,
    }
    out["theorem_B"] = {
        "live_closed_agree": b_agree,
        "live_closed_DISAGREE": b_disagree,
        "disagree_samples": b_disagree_sample,
        "not_live_closed_agree": nolc_agree,
        "not_live_closed_disagree": nolc_disagree,
        "not_live_closed_disagree_samples": nolc_sample,
        "systems_with_a_filled_set": filled_found,
    }

    gates = {
        # the theorem itself
        "A_sound": len(unsound_A) == 0,
        "A_hypotheses_nonvacuous": hyp_hold > 0 and table["wf_concl"] > 0,
        # WF is necessary for the conclusion, and not only sufficient: this is
        # what filled_set_obstruction composed with filledSetOfNotWellFounded
        # predicts, so an occupied nowf_concl cell would refute 0.5.0
        "A_wf_necessary": table["nowf_concl"] == 0,
        "A_wf_failure_population_nonempty": table["nowf_noconcl"] > 0,
        # WF alone is NOT sufficient, so live_closed and live_bound are not idle
        "A_wf_alone_insufficient": table["wf_noconcl"] > 0,
        # the three hypotheses are not merely sufficient for the theorem's own
        # conclusion over this box: they are exactly it
        "A_exact_for_the_conclusion": conclusion_holds == hyp_hold - len(unsound_A),
        # the equivalence
        "B_exact_under_live_closed": b_disagree == 0 and b_agree > 0,
        "B_live_closed_is_load_bearing": nolc_disagree > 0,
        "filled_sets_are_found": filled_found > 0,
    }
    out["gates"] = gates
    out["pass"] = all(gates.values())
    return out


def ablate(n_max=2):
    """Each hypothesis of theorem (A), replaced by `True` in turn.  A hypothesis
    whose removal leaves 0 unsound was never doing any work, and a 0-unsound
    headline for the full conjunction would then be evidence of nothing.  This
    is the anti-vacuity control for this script, matching `ablate.py` for the
    census predicate."""
    rows = {}
    for name in ("well_founded", "live_closed", "live_bound"):
        original = globals()[name]
        globals()[name] = (lambda *_a, **_k: True)
        try:
            r = run(n_max=n_max)
        finally:
            globals()[name] = original
        rows[name] = {"unsound": r["theorem_A"]["UNSOUND"],
                      "hypotheses_satisfied": r["theorem_A"]["hypotheses_satisfied"],
                      "sample": (r["theorem_A"]["unsound_samples"] or [None])[0]}
    rows["_gate"] = all(v["unsound"] > 0 for k, v in rows.items() if not k.startswith("_"))
    return rows


if __name__ == "__main__":
    n_max = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    result = run(n_max=n_max)
    result["ablation"] = ablate()
    result["gates"]["A_every_hypothesis_load_bearing"] = result["ablation"]["_gate"]
    result["pass"] = all(result["gates"].values())
    print(json.dumps(result, indent=1))
    raise SystemExit(0 if result["pass"] else 1)
