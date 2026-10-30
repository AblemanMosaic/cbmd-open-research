"""Few multi-input transitions: a fixed-parameter decision procedure.

Revision 0.4.0 shows preservation is coNP-complete once transitions may have
two input places; its hardness uses unboundedly many of them.  This checks the
procedure that is polynomial for each fixed number k of multi-input
transitions.

Single-input transitions are dual-Horn clauses, so their capacity-dead set is
closed under pointwise maximum (revision 0.6.0).  A multi-input transition is
blocked iff one of finitely many unit literals holds: an input place below its
demand (an upper bound), or some place overflowing (a lower bound)
(`blocked_by_some_literal`).  Choose one literal per multi-input transition --
at most (#inputs + P) options each -- and every branch is max-closed again: a
greatest admissible solution exists, and since lower bounds and ordinary
enabledness are upward-closed, that marking decides the branch.

This is the classical branching on a strong backdoor to Horn (Nishimura,
Ragde and Szeider), applied with bounded-integer threshold literals; it is not
claimed as a new technique.

Gates: exact against the dossier's semantics; both outcomes present; the
multi-input population non-empty; and each literal family ablated in turn,
each ablation required to break the procedure.
"""
from __future__ import annotations

import json
import os
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from petri import nets, preserves as _preserves


def exact(pre, post, cap, P, T):
    verdict, _w = _preserves(pre, post, cap, P, T)
    return verdict


def literals(pre, post, cap, t, P, use_ub=True, use_lb=True):
    out = []
    for q in range(P):
        if use_ub and pre[t][q] > 0:
            out.append(("ub", q, pre[t][q] - 1))
        need = cap[q] - post[t][q] + pre[t][q] + 1
        if use_lb and need <= cap[q]:
            out.append(("lb", q, max(need, 0)))
    return out


def decide(pre, post, cap, P, T, use_ub=True, use_lb=True):
    ins = [sum(1 for q in range(P) if pre[t][q] > 0) for t in range(T)]
    multi = [t for t in range(T) if ins[t] >= 2]
    single = [t for t in range(T) if ins[t] == 1]
    branches = 0
    for choice in product(*[literals(pre, post, cap, t, P, use_ub, use_lb) for t in multi]):
        branches += 1
        ub = list(cap)
        lb = [0] * P
        for kind, q, b in choice:
            if kind == "ub":
                ub[q] = min(ub[q], b)
            else:
                lb[q] = max(lb[q], b)
        m = list(ub)
        changed = True
        while changed:
            changed = False
            for t in single:
                s = next(q for q in range(P) if pre[t][q] > 0)
                if m[s] < pre[t][s]:
                    continue
                if all(m[q] - pre[t][q] + post[t][q] <= cap[q] for q in range(P)):
                    m[s] = pre[t][s] - 1
                    changed = True
        if any(m[q] < lb[q] for q in range(P)):
            continue
        if any(all(m[q] >= pre[t][q] for q in range(P)) for t in range(T)):
            return False, branches
    return True, branches


def census(P, T, maxw, capmax):
    row = {"box": {"places": P, "transitions": T, "max_arc_weight": maxw,
                   "max_capacity": capmax},
           "systems": 0, "with_multi_input": 0, "preserving": 0, "not_preserving": 0,
           "UNSOUND": 0, "INCOMPLETE": 0, "max_branches": 0,
           "ablation": {"no_upper_bound_literals": 0, "no_lower_bound_literals": 0},
           "samples": []}
    for pre, post in nets(P, T, maxw):
        for cap in product(range(capmax + 1), repeat=P):
            cap = list(cap)
            ok = exact(pre, post, cap, P, T)
            if ok is None:
                continue
            row["systems"] += 1
            if any(sum(1 for q in range(P) if pre[t][q] > 0) >= 2 for t in range(T)):
                row["with_multi_input"] += 1
            row["preserving" if ok else "not_preserving"] += 1
            pred, br = decide(pre, post, cap, P, T)
            row["max_branches"] = max(row["max_branches"], br)
            if pred and not ok:
                row["UNSOUND"] += 1
            elif ok and not pred:
                row["INCOMPLETE"] += 1
            if pred != ok and len(row["samples"]) < 3:
                row["samples"].append({"pre": pre, "post": post, "capacity": cap,
                                       "exact": ok, "procedure": pred})
            if decide(pre, post, cap, P, T, use_ub=False)[0] != ok:
                row["ablation"]["no_upper_bound_literals"] += 1
            if decide(pre, post, cap, P, T, use_lb=False)[0] != ok:
                row["ablation"]["no_lower_bound_literals"] += 1
    return row


def run(boxes=((2, 2, 1, 2), (2, 2, 2, 2), (3, 2, 1, 2), (2, 3, 1, 2))):
    rows = [census(*b) for b in boxes]
    tot = lambda k: sum(r[k] for r in rows)                      # noqa: E731
    abl = {k: sum(r["ablation"][k] for r in rows)
           for k in ("no_upper_bound_literals", "no_lower_bound_literals")}
    gates = {
        "procedure_is_exact": tot("UNSOUND") == 0 and tot("INCOMPLETE") == 0,
        "both_outcomes_occur": tot("preserving") > 0 and tot("not_preserving") > 0,
        "multi_input_population_nonempty": tot("with_multi_input") > 0,
        "both_literal_families_load_bearing": all(v > 0 for v in abl.values()),
    }
    return {"schema": "cbmd.petri-backdoor.v1",
            "censuses": rows,
            "totals": {"systems": tot("systems"),
                       "with_multi_input": tot("with_multi_input"),
                       "preserving": tot("preserving"),
                       "not_preserving": tot("not_preserving"),
                       "unsound": tot("UNSOUND"), "incomplete": tot("INCOMPLETE"),
                       "ablation_wrong": abl},
            "gates": gates, "pass": all(gates.values()),
            "nonclaims": [
                "the technique is the classical branching on a strong backdoor to Horn "
                "(Nishimura, Ragde and Szeider); only its application here is recorded",
                "the max-closure under chosen literals and the exhaustiveness of the "
                "branching are compiled; termination of each branch's lowering is the "
                "compiled argument of revision 0.7.0 with the capacities replaced by the "
                "chosen upper bounds, which is not separately compiled",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    r = run()
    print(json.dumps(r, indent=1))
    raise SystemExit(0 if r["pass"] else 1)
