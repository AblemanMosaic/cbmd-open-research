"""Does the one-input characterization survive weighted arcs?

Revision 0.3.0 characterizes unit-weight flow nets by a SET of places held
full.  With weights that normalization breaks: filling a place to capacity can
make a transition ordinarily enabled that was not, and nothing then blocks it.
So the obstruction has to carry LEVELS, not membership.

Weighted flow net: transition t takes w(t) tokens from src(t) and either puts
v(t) into dst(t) or discards them.  A marking m is bad when it is admissible,
some t has m(src t) >= w(t), and every t is blocked:

    m(src t) < w(t)                      (cannot fire)
 or dst t exists and m(dst t) + v(t) > C(dst t)      (would overflow)

Reading the second disjunct as an implication,

    m(src t) >= w(t)   ==>   m(dst t) >= C(dst t) - v(t) + 1

gives a monotone propagation.  Candidate algorithm: for each transition t0 in
turn, start from the least marking with m(src t0) = w(t0), close under the
implications, and accept if the closure stays inside the capacities and no
DRAIN has its source at or above its own weight.  Raising a marking only ever
makes the drain constraints harder, so the least closure is the best candidate
and testing it is enough.

Checked exhaustively against the exact semantics, with both outcomes gated.
"""
from __future__ import annotations

import json
import os
import sys
from itertools import combinations_with_replacement, product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from petri import preserves as _preserves


def exact(pre, post, cap, P, T):
    """This dossier's own semantics, which returns a (verdict, witness) pair."""
    verdict, _witness = _preserves(pre, post, cap, P, T)
    return verdict


def build(trs, P):
    """trs: (src, dst_or_None, w, v)."""
    T = len(trs)
    pre = [[0] * P for _ in range(T)]
    post = [[0] * P for _ in range(T)]
    for i, (s, d, w, v) in enumerate(trs):
        pre[i][s] = w
        if d is not None:
            post[i][d] = v
    return pre, post


def algorithm(trs, cap, P, skip_drain_check=False, skip_capacity_check=False,
              justify=None):
    """True when no bad marking exists.

    The closure never leaves the capacity box, so no in-loop capacity test is
    needed: a raise sets m[d] = cap[d] - v + 1 with v >= 1, which is at most
    cap[d].  Only the seed m[s0] = w(t0) can leave the box, so one check after
    the closure suffices.  An earlier draft tested the box inside the loop AND
    guarded the seed; ablating either changed nothing in any box, because each
    was covered by the other, and that is how the duplication was found.  The
    two remaining steps are each ablatable and are measured."""
    for t0 in trs:
        s0, _, w0, _ = t0
        m = [0] * P
        m[s0] = w0
        why = [None] * P
        why[s0] = ("seed",)
        changed = True
        while changed:
            changed = False
            for i, (s, d, w, v) in enumerate(trs):
                if m[s] >= w and d is not None and v <= cap[d]:
                    # the guard v <= cap[d] matters: a mover that produces more
                    # than the destination can hold is blocked whatever the
                    # destination holds, so it forces nothing
                    need = cap[d] - v + 1
                    if need > m[d]:
                        m[d] = need
                        why[d] = ("step", i)
                        changed = True
        if not skip_capacity_check and any(m[q] > cap[q] for q in range(P)):
            continue                                  # the seed alone can leave the box
        if not skip_drain_check and any(m[s] >= w for (s, d, w, v) in trs if d is None):
            continue                                  # a drain could fire: not dead
        if justify is not None:
            justify.append(check_justification(trs, cap, P, m, why, t0))
        return False                                  # bad marking found
    return True


def check_justification(trs, cap, P, m, why, t0):
    """Every non-zero level must carry a derivation in the sense of the Lean
    inductive `Forced`: either it is the seed, or it is `cap[d] - v + 1` for a
    mover whose source already reaches its own weight and whose production fits
    inside the destination's capacity.  The Lean completeness lemma takes
    exactly this as its hypothesis, so checking it here is what ties the proved
    statement to the procedure rather than assuming they match."""
    s0, _, w0, _ = t0
    for q in range(P):
        if m[q] == 0:
            continue
        tag = why[q]
        if tag is None:
            return False
        if tag[0] == "seed":
            if not (q == s0 and m[q] == w0):
                return False
        else:
            s, d, w, v = trs[tag[1]]
            if d != q or v > cap[q] or m[s] < w or m[q] != cap[q] - v + 1:
                return False
    return True


def transitions_for(P, maxw):
    out = []
    for s in range(P):
        for w in range(1, maxw + 1):
            out.append((s, None, w, 0))
            for d in range(P):
                if d == s:
                    continue
                for v in range(1, maxw + 1):
                    out.append((s, d, w, v))
    return out


def run(P, T, maxw, capmax):
    opts = transitions_for(P, maxw)
    agree = unsound = incomplete = pres = nonpres = 0
    samples = []
    abl = {"no_drain_check": {"UNSOUND": 0, "INCOMPLETE": 0},
           "no_capacity_check": {"UNSOUND": 0, "INCOMPLETE": 0}}
    justified_ok = justified_bad = 0
    for trs in combinations_with_replacement(opts, T):
        pre, post = build(trs, P)
        for cap in product(range(capmax + 1), repeat=P):
            ok = exact(pre, post, list(cap), P, len(trs))
            if ok is None:
                continue
            pres += ok; nonpres += (not ok)
            for name, kw in (("no_drain_check", {"skip_drain_check": True}),
                             ("no_capacity_check", {"skip_capacity_check": True})):
                pa = algorithm(trs, cap, P, **kw)
                if pa and not ok:
                    abl[name]["UNSOUND"] += 1
                elif ok and not pa:
                    abl[name]["INCOMPLETE"] += 1
            j = []
            pred = algorithm(trs, cap, P, justify=j)
            justified_ok += sum(1 for x in j if x)
            justified_bad += sum(1 for x in j if not x)
            if ok == pred:
                agree += 1
            elif pred and not ok:
                unsound += 1
                if len(samples) < 4:
                    samples.append({"transitions": [list(map(str, t)) for t in trs],
                                    "capacity": list(cap), "kind": "unsound"})
            else:
                incomplete += 1
                if len(samples) < 4:
                    samples.append({"transitions": [list(map(str, t)) for t in trs],
                                    "capacity": list(cap), "kind": "incomplete"})
    return {"box": {"P": P, "T": T, "maxw": maxw, "capmax": capmax},
            "agree": agree, "UNSOUND": unsound, "INCOMPLETE": incomplete,
            "preserving": pres, "not_preserving": nonpres,
            "nonvacuous": pres > 0 and nonpres > 0, "samples": samples,
            "ablation": abl,
            "justified_closures": justified_ok,
            "UNJUSTIFIED_closures": justified_bad}


BOXES = ((2, 2, 2, 2), (3, 2, 2, 2), (2, 3, 2, 2), (3, 3, 1, 2), (2, 3, 3, 3), (3, 3, 2, 1))


def report(boxes=BOXES):
    rows = [run(*b) for b in boxes]
    tot = lambda k: sum(r[k] for r in rows)                        # noqa: E731
    abl = {name: {kind: sum(r["ablation"][name][kind] for r in rows)
                  for kind in ("UNSOUND", "INCOMPLETE")}
           for name in ("no_drain_check", "no_capacity_check")}
    gates = {
        "every_accepted_closure_is_justified":
            tot("UNJUSTIFIED_closures") == 0 and tot("justified_closures") > 0,
        "algorithm_is_exact": tot("UNSOUND") == 0 and tot("INCOMPLETE") == 0,
        "both_outcomes_occur": tot("preserving") > 0 and tot("not_preserving") > 0,
        "each_step_is_load_bearing":
            all(v["UNSOUND"] + v["INCOMPLETE"] > 0 for v in abl.values()),
    }
    return {"schema": "cbmd.petri-weighted-flow.v1",
            "censuses": rows,
            "totals": {"systems": tot("agree") + tot("UNSOUND") + tot("INCOMPLETE"),
                       "preserving": tot("preserving"),
                       "not_preserving": tot("not_preserving"),
                       "unsound": tot("UNSOUND"),
                       "incomplete": tot("INCOMPLETE"),
                       "justified_closures": tot("justified_closures"),
                       "unjustified_closures": tot("UNJUSTIFIED_closures"),
                       "ablation": abl},
            "gates": gates,
            "pass": all(gates.values()),
            "nonclaims": [
                "soundness, the characterization, and the completeness of a justified "
                "closure are proved in verification/lean/; the termination of the "
                "closure iteration is a prose argument, not compiled",
                "finite censuses over the stated boxes",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    r = report()
    print(json.dumps(r, indent=1))
    raise SystemExit(0 if r["pass"] else 1)
