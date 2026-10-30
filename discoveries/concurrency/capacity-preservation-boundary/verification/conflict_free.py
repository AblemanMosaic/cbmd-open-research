"""Conflict-free nets are polynomial; one conflict place is coNP-complete
(revision 0.12.0).

A net is CONFLICT-FREE when every place has at most one consuming transition.
Assume, as everywhere in this dossier's censuses and reductions, that every
transition has at least one input place.  Then preservation is decidable in
polynomial time, at arbitrary weights and capacities.  The free-choice nets of
revision 0.10.0 have exactly ONE place with several consumers, so the boundary
is sharp: zero conflict places, polynomial; one, coNP-complete.

## The procedure (written argument)

Fix the transition t0 that a bad marking ordinarily enables; its inputs get a
floor lo(q) = pre(t0,q).  A transition is OBLIGATED when all its inputs are
high enough that only an overflow can block it.  t0 is obligated.  An
obligated t chooses an output q with post > pre whose overflow threshold
b = max(cap - post + pre + 1, lo(q)) is at most cap(q).  Setting m(q) = b:

  * if q has no consumer, or its consumer is t itself or t0, or its consumer
    has two or more inputs, or the consumer's own lower literal still holds at
    b (b <= pre(c,q) - 1), the chain ENDS successfully: every other input of a
    multi-input consumer stays at 0, because no other chain feeds it;
  * otherwise the single-input consumer c is now ordinarily enabled and becomes
    obligated: the chain continues at c.

A bad marking with this t0 exists iff t0 survives the greatest fixpoint
    Alive = { t : some option of t ends, or leads into Alive }.
Completeness: the transitions ordinarily enabled at a bad marking form a
post-fixpoint, so they are all Alive.  Soundness: follow one option per Alive
transition from t0; set only the chosen places (and t0's inputs) high and every
other place to 0.  A transition off the chain has an input at 0 -- this is
where "every transition has an input place" is used -- unless all its inputs
are on the chain, which conflict-freeness rules out: each chain place feeds
one consumer, and a chain ends at the first multi-input consumer it meets.

## Gates

  * exact against brute force over all admissible markings;
  * BRIDGE: the compiled statement `not_preserves_iff_certificate` is about
    `Certificate`; a literal transcription of it, decided by brute force over
    every candidate set R and value v, must agree with the fixpoint procedure;
  * both outcomes, and multi-input non-preserving nets, occur;
  * every generated net is conflict-free with an input place on every
    transition, checked;
  * ABLATIONS, each must give wrong verdicts: no t0 floor; a multi-input
    consumer treated as continuing; the consumer's lower literal ignored;
  * HYPOTHESIS: on nets that DO have input-less transitions the procedure must
    be wrong somewhere -- otherwise the hypothesis would be idle;
  * SHARPNESS: every free-choice net of revision 0.10.0 has exactly one place
    with more than one consumer.
"""
from __future__ import annotations

import json
import os
import random
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from marked_graph import brute  # noqa: E402


def consumers(pre, P, T, q):
    return [t for t in range(T) if pre[t][q] > 0]


def conflict_places(pre, P, T):
    return sum(1 for q in range(P) if len(consumers(pre, P, T, q)) > 1)


def bad_with(pre, post, cap, P, T, t0, ablate=None):
    lo = [0] * P if ablate == "no_t0_floor" else [pre[t0][q] for q in range(P)]
    if any(lo[q] > cap[q] for q in range(P)):
        return False
    cons = [(consumers(pre, P, T, q) or [None])[0] for q in range(P)]
    ninp = [sum(1 for q in range(P) if pre[t][q] > 0) for t in range(T)]

    def options(t):
        out = []
        for q in range(P):
            if post[t][q] <= pre[t][q]:
                continue
            b = max(cap[q] - post[t][q] + pre[t][q] + 1, lo[q])
            if b > cap[q]:
                continue
            c = cons[q]
            if c is None or c == t or c == t0:
                out.append("END")
            elif ninp[c] >= 2 and ablate != "multi_input_continues":
                out.append("END")
            elif b <= pre[c][q] - 1 and ablate != "ignore_consumer_literal":
                out.append("END")
            else:
                out.append(c)
        return out
    opts = [options(t) for t in range(T)]
    alive = set(range(T))
    changed = True
    while changed:
        changed = False
        for t in list(alive):
            if not any(o == "END" or o in alive for o in opts[t]):
                alive.discard(t)
                changed = True
    return t0 in alive


def lean_certificate(pre, post, cap, P, T):
    """Literal transcription of ConflictFree.Certificate (Lean), decided by
    brute force over every candidate R and every value v -- no fixpoint, no
    threshold arithmetic.  Used to bridge the compiled statement to `decide`."""
    def opt(t0, t, q, v):
        return v <= cap[q] and pre[t0][q] <= v and cap[q] < max(v - pre[t][q], 0) + post[t][q]

    def ends(t0, t, q, v):
        return (all(pre[c][q] == 0 for c in range(T)) or pre[t][q] > 0 or pre[t0][q] > 0
                or any(pre[c][q] > 0 and pre[c][r] > 0 and r != q
                       for c in range(T) for r in range(P))
                or any(pre[c][q] > 0 and v < pre[c][q] for c in range(T)))
    for t0 in range(T):
        if any(pre[t0][q] > cap[q] for q in range(P)):
            continue
        for mask in range(1 << T):
            if not mask >> t0 & 1:
                continue
            R = {t for t in range(T) if mask >> t & 1}
            if all(any(opt(t0, t, q, v) and (ends(t0, t, q, v) or
                                             all(c in R for c in range(T) if pre[c][q] > 0))
                       for q in range(P) for v in range(cap[q] + 1))
                   for t in R):
                return True
    return False


def decide(pre, post, cap, P, T, ablate=None):
    """True iff the net preserves."""
    return not any(bad_with(pre, post, cap, P, T, t0, ablate) for t0 in range(T))


def random_conflict_free(rng, P, T, w, capmax, density, need_inputs=True):
    while True:
        pre = [[0] * P for _ in range(T)]
        post = [[0] * P for _ in range(T)]
        for q in range(P):
            c = rng.randrange(T + 1)
            if c < T:
                pre[c][q] = rng.randint(1, w)
            for t in range(T):
                if rng.random() < density:
                    post[t][q] = rng.randint(1, w)
        has_inputs = all(any(pre[t][q] for q in range(P)) for t in range(T))
        if has_inputs == need_inputs:
            return pre, post, [rng.randint(0, capmax) for _ in range(P)]


def run(trials=20000, seed=5):
    rng = random.Random(seed)
    agree = disagree = pres = nonpres = multi = multi_np = shape_bad = bridge_bad = 0
    abl = {"no_t0_floor": 0, "multi_input_continues": 0, "ignore_consumer_literal": 0}
    samples = []
    for _ in range(trials):
        P = rng.randint(1, 5)
        T = rng.randint(1, min(P, 4))
        pre, post, cap = random_conflict_free(rng, P, T, rng.choice([1, 2, 3]),
                                              rng.choice([1, 2, 3]), rng.choice([0.2, 0.4, 0.6]))
        shape_bad += conflict_places(pre, P, T) != 0 or \
            not all(any(pre[t][q] for q in range(P)) for t in range(T))
        truth = brute(pre, post, cap, P, T)
        pres += truth
        nonpres += not truth
        if any(sum(1 for q in range(P) if pre[t][q]) >= 2 for t in range(T)):
            multi += 1
            multi_np += not truth
        verdict = decide(pre, post, cap, P, T)
        bridge_bad += lean_certificate(pre, post, cap, P, T) != (not verdict)
        if verdict == truth:
            agree += 1
        else:
            disagree += 1
            if len(samples) < 3:
                samples.append({"pre": pre, "post": post, "cap": cap, "preserves": truth})
        for a in abl:
            abl[a] += decide(pre, post, cap, P, T, a) != truth
    # the input-place hypothesis, tested on nets that violate it
    rng2 = random.Random(seed + 1)
    inputless_wrong = 0
    for _ in range(trials // 4):
        P, T = rng2.randint(1, 4), rng2.randint(1, 4)
        pre, post, cap = random_conflict_free(rng2, P, T, 2, 2, 0.4, need_inputs=False)
        inputless_wrong += decide(pre, post, cap, P, T) != brute(pre, post, cap, P, T)
    # sharpness: the 0.10.0 free-choice nets have exactly one conflict place
    from free_choice import fc_net, population
    conflict_counts = sorted({conflict_places(r[0], r[3], r[4])
                              for r in (fc_net(n, cnf) for n, cnf in population(20))})
    gates = {
        "procedure_is_exact": disagree == 0 and agree > 0,
        "bridge_lean_certificate_matches_procedure": bridge_bad == 0,
        "both_outcomes_occur": pres > 0 and nonpres > 0,
        "multi_input_population_nonempty": multi > 0 and multi_np > 0,
        "every_net_conflict_free_with_inputs": shape_bad == 0,
        "ablation_no_t0_floor_breaks": abl["no_t0_floor"] > 0,
        "ablation_multi_input_continues_breaks": abl["multi_input_continues"] > 0,
        "ablation_ignore_consumer_literal_breaks": abl["ignore_consumer_literal"] > 0,
        "input_place_hypothesis_load_bearing": inputless_wrong > 0,
        "free_choice_nets_have_exactly_one_conflict_place": conflict_counts == [1],
    }
    return {"schema": "cbmd.petri-conflict-free.v1", "nets": trials,
            "agree": agree, "disagree": disagree, "bridge_mismatches": bridge_bad,
            "preserving": pres, "not_preserving": nonpres,
            "with_multi_input_transition": multi,
            "with_multi_input_not_preserving": multi_np,
            "ablation_wrong_verdicts": abl,
            "inputless_nets_wrong_verdicts": inputless_wrong,
            "free_choice_conflict_place_counts": conflict_counts,
            "samples": samples, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": [
                "the characterization is compiled (ConflictFree.lean); that the greatest-fixpoint procedure decides the certificate is the standard Knaster-Tarski step, bridged here by census rather than compiled",
                "nets with input-less transitions are excluded, and the procedure is demonstrably wrong on them; their complexity is open",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 20000)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
