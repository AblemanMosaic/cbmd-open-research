"""Does a capacity constraint introduce NEW dead markings in a Petri net?

Chip-firing is the special case where every place is consumed by exactly one
transition (the vertex's own firing) and that transition consumes only from it.
The preservation theorem proved there rests on: a blocked sender implies a full
receiver, and a full receiver is itself above its own firing threshold.

In a general net a place may be consumed by a transition that also needs other
places, so "q is full" no longer implies anything is enabled. This asks how far
the theorem survives.

Exact question, which needs no confluence:

    PRESERVES(N, C)  <=>  every capacity-reachable marking that is capacity-dead
                          is also dead in the uncapacitated net

Capacity-dead but ordinarily enabled = a deadlock the capacity invented.
"""
from __future__ import annotations

import json
from itertools import product


def ordinarily_enabled(pre, m, t, P):
    return all(m[q] >= pre[t][q] for q in range(P))


def capacity_enabled(pre, post, cap, m, t, P):
    if not ordinarily_enabled(pre, m, t, P):
        return False
    return all(m[q] - pre[t][q] + post[t][q] <= cap[q] for q in range(P))


def fire(pre, post, m, t, P):
    return tuple(m[q] - pre[t][q] + post[t][q] for q in range(P))


def capacity_reachable(pre, post, cap, m0, P, T, limit=100000):
    seen = {m0}
    stack = [m0]
    while stack:
        m = stack.pop()
        for t in range(T):
            if capacity_enabled(pre, post, cap, m, t, P):
                n = fire(pre, post, m, t, P)
                if n not in seen:
                    if len(seen) > limit:
                        return None
                    seen.add(n)
                    stack.append(n)
    return seen


def preserves(pre, post, cap, P, T):
    """False with a witness if some capacity-reachable capacity-dead marking is
    ordinarily enabled. Checked from every admissible initial marking."""
    for m0 in product(*(range(c + 1) for c in cap)):
        reach = capacity_reachable(pre, post, cap, m0, P, T)
        if reach is None:
            return None, None
        for m in reach:
            if any(capacity_enabled(pre, post, cap, m, t, P) for t in range(T)):
                continue
            live = [t for t in range(T) if ordinarily_enabled(pre, m, t, P)]
            if live:
                return False, {"initial": list(m0), "dead_marking": list(m),
                               "ordinarily_enabled": live}
    return True, None


# ------------------------------------------------------------------ candidates
def gain(pre, post, t, q):
    return post[t][q] - pre[t][q]


def chipfiring_shaped(pre, post, P, T):
    """Each transition consumes from exactly one place, and distinct transitions
    consume from distinct places: the chip-firing shape."""
    consumed = []
    for t in range(T):
        qs = [q for q in range(P) if pre[t][q] > 0]
        if len(qs) != 1:
            return False
        consumed.append(qs[0])
    return len(set(consumed)) == T


def chipfiring_bound(pre, post, cap, P, T):
    """The live-set bound, read in net terms: for every transition t and place q
    that t feeds, the capacity of q admits t's bundle on top of the threshold of
    the transition consuming q."""
    for t in range(T):
        for q in range(P):
            if post[t][q] <= 0:
                continue
            consumers = [s for s in range(T) if pre[s][q] > 0]
            if not consumers:
                return False                       # nothing can ever drain q
            if not any(pre[s][q] + post[t][q] <= cap[q] + 1 for s in consumers):
                return False
    return True


def nonbinding(pre, post, cap, P, T):
    """Capacity never blocks an ordinarily enabled transition, at any admissible
    marking: for every t and q, firing t from a full-as-possible q stays inside."""
    for t in range(T):
        for q in range(P):
            if cap[q] - pre[t][q] + post[t][q] > cap[q] and gain(pre, post, t, q) > 0:
                # the binding case: an ordinarily enabled t can overflow q
                return False
    return True


def nets(P, T, maxw):
    """Loop-free-ish small nets: every transition consumes something and produces
    something or is a drain; no transition is the identity."""
    cells = P * T
    for pv in product(range(maxw + 1), repeat=cells):
        pre = [[pv[t * P + q] for q in range(P)] for t in range(T)]
        if any(all(v == 0 for v in pre[t]) for t in range(T)):
            continue                                # a transition with no input always fires
        for qv in product(range(maxw + 1), repeat=cells):
            post = [[qv[t * P + q] for q in range(P)] for t in range(T)]
            if all(pre[t] == post[t] for t in range(T)):
                continue                            # no net effect at all
            yield pre, post


def run(P=2, T=2, maxw=2, capmax=3):
    tally = {"nets": 0, "systems": 0, "preserving": 0, "not_preserving": 0, "skipped": 0}
    conf = {"cf_and_bound": [0, 0], "nonbinding": [0, 0]}   # [pred&pres, pred&!pres]
    cf_counter = None
    examples = []
    for pre, post in nets(P, T, maxw):
        tally["nets"] += 1
        for cap in product(range(capmax + 1), repeat=P):
            tally["systems"] += 1
            ok, witness = preserves(pre, post, list(cap), P, T)
            if ok is None:
                tally["skipped"] += 1
                continue
            tally["preserving" if ok else "not_preserving"] += 1
            cf = chipfiring_shaped(pre, post, P, T) and chipfiring_bound(pre, post, list(cap), P, T)
            nb = nonbinding(pre, post, list(cap), P, T)
            conf["cf_and_bound"][0 if ok else 1] += 1 if cf else 0
            conf["nonbinding"][0 if ok else 1] += 1 if nb else 0
            if cf and not ok and cf_counter is None:
                cf_counter = {"pre": pre, "post": post, "capacity": list(cap), **witness}
            if nb and not ok and len(examples) < 3:
                examples.append({"pre": pre, "post": post, "capacity": list(cap), **witness})
    return {"schema": "cbmd.petri-capacity-preservation.v1",
            "box": {"places": P, "transitions": T, "max_arc_weight": maxw, "max_capacity": capmax},
            "tally": tally,
            "chipfiring_shape_and_bound": {"preserving": conf["cf_and_bound"][0],
                                           "NOT_preserving": conf["cf_and_bound"][1],
                                           "counterexample": cf_counter},
            "nonbinding_capacity": {"preserving": conf["nonbinding"][0],
                                    "NOT_preserving": conf["nonbinding"][1],
                                    "counterexamples": examples}}


if __name__ == "__main__":
    print(json.dumps(run(), indent=1))
