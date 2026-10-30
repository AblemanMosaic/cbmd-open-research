"""One input place is the whole story: outputs and weights are free.

The dichotomy of revision 0.4.0 is stated in INPUT places, and its hardness
construction uses only that a transition's ordinary enabledness is a
conjunction over its inputs.  Outputs play no part.  So the polynomial side
ought to cover any number of outputs — which the flow family of revision 0.5.0
does not, since each of its transitions feeds at most one place.

It does, and for a reason that collapses the whole single-input case to a
single marking.  With one input place, "m is capacity-dead" is a clause per
transition with exactly ONE negative literal — `not (w(t) <= m(input t))` —
and one positive literal per place that firing would overflow.  Such a system
is closed under pointwise maximum, so there is a greatest capacity-dead
admissible marking M, and since ordinary enabledness is monotone in m,

    PRESERVES(N, C)   <=>   M is ordinarily dead.

`capDead_max` in verification/lean/ is the closure lemma and is where the
single-input hypothesis is spent.

## The algorithm, and its certificate

    M := C
    repeat: if some transition is capacity-enabled at M, lower its input place
            to one below its own weight
    until stable

Each lowering is justified: for any capacity-dead m below the current vector
u, if m reached that transition's weight it would be capacity-enabled there,
because the overflow test is monotone in the marking.  That justification is
the inductive predicate `Capped` in the Lean development, and the procedure
emits it here so a checker can validate it rather than the proof assuming the
procedure did the right thing.

## Gates

  * the algorithm agrees with the exact semantics, with both outcomes present;
  * every accepted run carries a `Capped` derivation that replays correctly;
  * each step of the algorithm is ablatable and each ablation breaks it.
"""
from __future__ import annotations

import json
import os
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from petri import preserves as _preserves


def exact(pre, post, cap, P, T):
    verdict, _witness = _preserves(pre, post, cap, P, T)
    return verdict


def input_place(pre, t, P):
    return next(q for q in range(P) if pre[t][q] > 0)


def greatest_model(pre, post, cap, P, T, certificate=None,
                   skip_fits=False, single_pass=False):
    """Lower from the capacities until nothing is capacity-enabled."""
    m = list(cap)
    rounds = 0
    changed = True
    while changed:
        changed = False
        rounds += 1
        for t in range(T):
            s = input_place(pre, t, P)
            w = pre[t][s]
            if m[s] < w:
                continue
            fits = all(m[q] - pre[t][q] + post[t][q] <= cap[q] for q in range(P))
            if skip_fits or fits:
                if certificate is not None:
                    certificate.append(t)
                m[s] = w - 1
                changed = True
        if single_pass:
            break
    return m


def ordinarily_dead(pre, m, P, T):
    return not any(all(pre[t][q] <= m[q] for q in range(P)) for t in range(T))


def replay_certificate(pre, post, cap, P, T, steps, final):
    """Re-derive the certificate from scratch, in the shape of the inductive
    `Capped`: start at the capacities, and accept a step only when the
    transition really would be capacity-enabled at the vector reached so far."""
    u = list(cap)
    for t in steps:
        if not all(u[q] - pre[t][q] + post[t][q] <= cap[q] for q in range(P)):
            return False
        s = input_place(pre, t, P)
        u[s] = pre[t][s] - 1
    return u == final


def single_input_nets(P, T, maxw, capmax):
    inputs = [(s, w) for s in range(P) for w in range(1, maxw + 1)]
    outs = list(product(range(maxw + 1), repeat=P))
    for choice in product(range(len(inputs)), repeat=T):
        pre = []
        for i in choice:
            s, w = inputs[i]
            pre.append([w if q == s else 0 for q in range(P)])
        for og in product(range(len(outs)), repeat=T):
            post = [list(outs[j]) for j in og]
            if all(pre[t] == post[t] for t in range(T)):
                continue
            for cap in product(range(capmax + 1), repeat=P):
                yield pre, post, list(cap)


def census(P, T, maxw, capmax):
    row = {"box": {"places": P, "transitions": T, "max_arc_weight": maxw,
                   "max_capacity": capmax},
           "systems": 0, "preserving": 0, "not_preserving": 0,
           "UNSOUND": 0, "INCOMPLETE": 0, "samples": [],
           "certificates_replayed": 0, "CERTIFICATES_FAILED": 0,
           "ablation": {"no_fits_test": {"wrong": 0}, "single_pass": {"wrong": 0}}}
    for pre, post, cap in single_input_nets(P, T, maxw, capmax):
        ok = exact(pre, post, cap, P, T)
        if ok is None:
            continue
        row["systems"] += 1
        row["preserving" if ok else "not_preserving"] += 1

        cert = []
        M = greatest_model(pre, post, cap, P, T, certificate=cert)
        pred = ordinarily_dead(pre, M, P, T)
        if replay_certificate(pre, post, cap, P, T, cert, M):
            row["certificates_replayed"] += 1
        else:
            row["CERTIFICATES_FAILED"] += 1

        if pred and not ok:
            row["UNSOUND"] += 1
            if len(row["samples"]) < 4:
                row["samples"].append({"pre": pre, "post": post,
                                       "capacity": cap, "kind": "unsound"})
        elif ok and not pred:
            row["INCOMPLETE"] += 1
            if len(row["samples"]) < 4:
                row["samples"].append({"pre": pre, "post": post,
                                       "capacity": cap, "kind": "incomplete"})

        for name, kw in (("no_fits_test", {"skip_fits": True}),
                         ("single_pass", {"single_pass": True})):
            Ma = greatest_model(pre, post, cap, P, T, **kw)
            if ordinarily_dead(pre, Ma, P, T) != ok:
                row["ablation"][name]["wrong"] += 1
    return row


def run(boxes=((2, 2, 1, 2), (2, 2, 2, 2), (3, 2, 1, 2), (2, 3, 1, 2))):
    rows = [census(*b) for b in boxes]
    tot = lambda k: sum(r[k] for r in rows)                        # noqa: E731
    abl = {name: sum(r["ablation"][name]["wrong"] for r in rows)
           for name in ("no_fits_test", "single_pass")}
    gates = {
        "algorithm_is_exact": tot("UNSOUND") == 0 and tot("INCOMPLETE") == 0,
        "both_outcomes_occur": tot("preserving") > 0 and tot("not_preserving") > 0,
        "every_certificate_replays":
            tot("CERTIFICATES_FAILED") == 0 and tot("certificates_replayed") > 0,
        "each_step_is_load_bearing": all(v > 0 for v in abl.values()),
    }
    return {"schema": "cbmd.petri-single-input.v1",
            "censuses": rows,
            "totals": {"systems": tot("systems"),
                       "preserving": tot("preserving"),
                       "not_preserving": tot("not_preserving"),
                       "unsound": tot("UNSOUND"),
                       "incomplete": tot("INCOMPLETE"),
                       "certificates_replayed": tot("certificates_replayed"),
                       "certificates_failed": tot("CERTIFICATES_FAILED"),
                       "ablation_wrong": abl},
            "gates": gates,
            "pass": all(gates.values()),
            "nonclaims": [
                "the closure lemma and the reduction of preservation to the greatest "
                "capacity-dead marking are proved in verification/lean/; the "
                "termination of the lowering iteration is a prose argument",
                "single input place per transition; outputs and weights unconstrained",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    r = run()
    print(json.dumps(r, indent=1))
    raise SystemExit(0 if r["pass"] else 1)
