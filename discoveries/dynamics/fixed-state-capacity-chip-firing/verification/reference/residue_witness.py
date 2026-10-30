"""Getting stuck on the star versus the residue witness.

`Stuck.lean` proves one direction: a bin run that gets stuck yields a
**residue witness** -- a set F of senders, missing at least one, such that every
sender outside F overflows the receiver on top of (sum F) mod B
(`stuck_imp_witness`); hence no witness means no bad ending
(`safe_of_no_witness`).

The other direction -- every residue witness is realised by some stuck run --
is a CONJECTURE.  This script checks both directions exhaustively on every
multiset of bundles in the stated range, and checks a pseudo-polynomial decider
for the witness condition against the definition.

Gates (each required):
  * SOUND (the proved direction): every instance with a reachable stuck run has
    a residue witness;
  * CONJECTURE: every instance with a residue witness has a reachable stuck run
    (no counterexample in range; this is evidence, not proof);
  * DP: the O(k^2 B) residue decider agrees with the witness definition;
  * SIMULATION: on random stars the bin-run "stuck" predicate agrees with the
    weighted dossier's exact simulator of capacity firing;
  * CONTROLS, each of which must bite:
      - a single-bin rule (no exact resets) misses stuck runs somewhere, so full
        bins matter;
      - a witness rule with >= in place of > accepts some instance with no stuck
        run, so the strict inequality is load-bearing;
      - largest-fit and smallest-fit greedy runs each fail to find a stuck run
        on some instance that has one, so the question is not settled by a
        fixed greedy order;
  * SCOPE: with two receivers the residue condition is necessary but NOT
    sufficient -- an explicit two-receiver system has a residue witness and,
    by exact simulation, no reachable bad terminal state -- so the conjecture
    is specific to the single-receiver star;
  * OBSERVATIONS (recorded, not gated): whether some witness of minimum fired
    total has a fired set that some order packs completely, whether the
    largest-fit order does, and whether every order does.  The every-order form held up to B = 10, k = 6 and FAILS in the
    larger range (B <= 13, k <= 8), so it is not a route to a proof.
"""
from __future__ import annotations

import itertools
import json
import random
import sys
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
WEIGHTED = HERE.parents[2] / "weighted-capacity-chip-firing" / "verification" / "reference"
sys.path.insert(0, str(WEIGHTED))
from characterize import cap_terminals, ordinary_normal  # noqa: E402

B_MAX = int(sys.argv[2]) if len(sys.argv) > 2 else 13
K_MAX = int(sys.argv[3]) if len(sys.argv) > 3 else 8


def stuck_reachable(a, B):
    """Some bin run (Lean `Run`) gets stuck: fill < B, a sender unfired, none fits."""
    k = len(a)
    full = (1 << k) - 1
    seen = set()
    stack = [(0, 0)]
    while stack:
        m, f = stack.pop()
        if (m, f) in seen:
            continue
        seen.add((m, f))
        if f == B:
            stack.append((m, 0))
            continue
        fit = [i for i in range(k) if not m >> i & 1 and f + a[i] <= B]
        if not fit and m != full:
            return True
        for i in fit:
            stack.append((m | 1 << i, f + a[i]))
    return False


def single_bin_stuck(a, B):
    k = len(a)
    for m in range((1 << k) - 1):
        s = sum(a[i] for i in range(k) if m >> i & 1)
        if s < B and all(s + a[i] > B for i in range(k) if not m >> i & 1):
            return True
    return False


def witnesses(a, B, strict=True):
    """Residue witnesses, from the Lean definition `ResidueWitness`."""
    k = len(a)
    out = []
    for m in range((1 << k) - 1):  # F must miss some sender
        r = sum(a[i] for i in range(k) if m >> i & 1) % B
        if all((r + a[i] > B) if strict else (r + a[i] >= B)
               for i in range(k) if not m >> i & 1):
            out.append(m)
    return out


def dp_witness(a, B):
    """Pseudo-polynomial decider: sort; let j be the smallest unfired sender
    (all smaller ones fired); the senders after j are optional; ask whether some
    residue r reachable as (prefix + optional subset) mod B has r + a_j > B."""
    v = sorted(a)
    k = len(v)
    suffix = [None] * (k + 1)
    reach = {0}
    suffix[k] = frozenset(reach)
    for i in range(k - 1, -1, -1):
        reach = reach | {(x + v[i]) % B for x in reach}
        suffix[i] = frozenset(reach)
    prefix = 0
    for j in range(k):
        if any((prefix + x) % B + v[j] > B for x in suffix[j + 1]):
            return True
        prefix += v[j]
    return False


def greedy_stuck(a, B, pick):
    rem = sorted(a)
    f = 0
    while rem:
        if f == B:
            f = 0
        fit = [x for x in rem if f + x <= B]
        if not fit:
            return True
        x = pick(fit)
        rem.remove(x)
        f += x
    return False


def some_order_completes(G, B):
    @lru_cache(None)
    def go(rem, f):
        if f == B:
            return go(rem, 0)
        if not rem:
            return True
        return any(go(rem[:i] + rem[i + 1:], f + rem[i])
                   for i, x in enumerate(rem) if f + x <= B and (i == 0 or rem[i - 1] != x))
    return go(tuple(sorted(G)), 0)


def every_order_completes(G, B):
    @lru_cache(None)
    def go(rem, f):
        if f == B:
            return go(rem, 0)
        if not rem:
            return True
        fit = [i for i, x in enumerate(rem) if f + x <= B]
        if not fit:
            return False
        return all(go(rem[:i] + rem[i + 1:], f + rem[i]) for i in fit)
    return go(tuple(sorted(G)), 0)


def star(a, B):
    k = len(a)
    n = k + 1
    A = [[0] * n for _ in range(n)]
    for i in range(k):
        A[i][k] = a[i]
    s = [0] * k + [B]
    c = list(a) + [B]
    return A, s, c, n, tuple(a) + (0,)


def simulated_bad(a, B):
    A, s, c, n, x = star(a, B)
    T = cap_terminals(A, s, c, n, x)
    onf = ordinary_normal(A, s, n, x)
    return any(t != onf for t in T)


TWO_RECEIVER = ([[3, 1], [1, 2], [3, 3], [0, 2], [0, 1]], [4, 6])


def two_receiver_system(A, Bs):
    """Senders i hold sum_j A[i][j] chips (outdegree = capacity = that), feeding
    receivers j (outdegree = capacity = Bs[j]) which drain to the sink."""
    k, d = len(A), len(Bs)
    n = k + d
    M = [[0] * n for _ in range(n)]
    for i in range(k):
        for j in range(d):
            M[i][k + j] = A[i][j]
    s = [0] * k + list(Bs)
    out = [sum(row) for row in A] + list(Bs)
    x = tuple(sum(row) for row in A) + (0,) * d
    return M, s, out, n, x


def residue_witness_multi(A, Bs):
    k, d = len(A), len(Bs)
    found = []
    for m in range((1 << k) - 1):
        r = [sum(A[i][j] for i in range(k) if m >> i & 1) % Bs[j] for j in range(d)]
        if all(any(r[j] + A[i][j] > Bs[j] for j in range(d)) for i in range(k) if not m >> i & 1):
            found.append(m)
    return found


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 20261030
    rng = random.Random(seed)
    counts = dict(instances=0, stuck=0, witness=0, sound_fail=0, conj_fail=0, dp_fail=0,
                  single_bin_misses=0, nonstrict_false_accepts=0,
                  largest_fit_misses=0, smallest_fit_misses=0,
                  min_total_witness_not_every_order=0, min_total_witness_not_packable=0,
                  min_total_witness_not_largest_fit=0,
                  oversize_instances=0)
    examples = {}
    for B in range(1, B_MAX + 1):
        for k in range(1, K_MAX + 1):
            top = B + 1 if k <= 4 else B  # include bundles too big ever to fire, for small k
            for a in itertools.combinations_with_replacement(range(1, top + 1), k):
                counts["instances"] += 1
                counts["oversize_instances"] += any(x > B for x in a)
                st = stuck_reachable(a, B)
                W = witnesses(a, B)
                w = bool(W)
                counts["stuck"] += st
                counts["witness"] += w
                if st and not w:
                    counts["sound_fail"] += 1
                    examples.setdefault("sound_fail", [a, B])
                if w and not st:
                    counts["conj_fail"] += 1
                    examples.setdefault("conj_fail", [a, B])
                if dp_witness(a, B) != w:
                    counts["dp_fail"] += 1
                    examples.setdefault("dp_fail", [a, B])
                if st and not single_bin_stuck(a, B):
                    counts["single_bin_misses"] += 1
                    examples.setdefault("single_bin_miss", [a, B])
                if not st and witnesses(a, B, strict=False):
                    counts["nonstrict_false_accepts"] += 1
                    examples.setdefault("nonstrict_false_accept", [a, B])
                if st and not greedy_stuck(a, B, max):
                    counts["largest_fit_misses"] += 1
                if st and not greedy_stuck(a, B, min):
                    counts["smallest_fit_misses"] += 1
                if w and all(x <= B for x in a):
                    k_ = len(a)
                    fired = [[a[i] for i in range(k_) if m >> i & 1] for m in W]
                    low = min(sum(F) for F in fired)
                    lows = [F for F in fired if sum(F) == low]
                    if not any(every_order_completes(F, B) for F in lows):
                        counts["min_total_witness_not_every_order"] += 1
                        examples.setdefault("min_total_witness_not_every_order", [a, B])
                    if not any(not greedy_stuck(F, B, max) for F in lows):
                        counts["min_total_witness_not_largest_fit"] += 1
                        examples.setdefault("min_total_witness_not_largest_fit", [a, B])
                    if not any(some_order_completes(F, B) for F in lows):
                        counts["min_total_witness_not_packable"] += 1
                        examples.setdefault("min_total_witness_not_packable", [a, B])
    # simulation tie-in on random stars
    sim = dict(samples=0, disagreements=0)
    for _ in range(400):
        B = rng.randint(1, 8)
        k = rng.randint(1, 5)
        a = tuple(rng.randint(1, B) for _ in range(k))
        sim["samples"] += 1
        if simulated_bad(a, B) != stuck_reachable(a, B):
            sim["disagreements"] += 1
            examples.setdefault("simulation_disagreement", [a, B])
    A2, B2 = TWO_RECEIVER
    M, s2, c2, n2, x2 = two_receiver_system(A2, B2)
    T2 = cap_terminals(M, s2, c2, n2, x2)
    onf2 = ordinary_normal(M, s2, n2, x2)
    two = {"system": {"A": A2, "B": B2},
           "residue_witnesses": [[i for i in range(len(A2)) if w >> i & 1]
                                 for w in residue_witness_multi(A2, B2)],
           "terminal_states": len(T2) if T2 is not None else None,
           "bad_terminal_reachable": (any(t != onf2 for t in T2) if T2 is not None else None)}
    gates = {
        "SOUND_stuck_implies_witness": counts["sound_fail"] == 0 and counts["stuck"] > 0,
        "CONJECTURE_witness_implies_stuck_no_counterexample": counts["conj_fail"] == 0,
        "DP_decider_matches_definition": counts["dp_fail"] == 0,
        "SIMULATION_agrees": sim["disagreements"] == 0 and sim["samples"] > 0,
        "CONTROL_single_bin_rule_bites": counts["single_bin_misses"] > 0,
        "CONTROL_nonstrict_rule_bites": counts["nonstrict_false_accepts"] > 0,
        "CONTROL_largest_fit_greedy_bites": counts["largest_fit_misses"] > 0,
        "CONTROL_smallest_fit_greedy_bites": counts["smallest_fit_misses"] > 0,
        "oversize_bundles_covered": counts["oversize_instances"] > 0,
        "SCOPE_two_receivers_witness_not_sufficient":
            bool(two["residue_witnesses"]) and two["bad_terminal_reachable"] is False,
    }
    out = {"schema": "cbmd.fixed-state-residue-witness.v1",
           "range": {"B": [1, B_MAX], "k": [1, K_MAX],
                     "bundles": "all multisets with entries 1..B (1..B+1 when k <= 4)"},
           "seed": seed, "counts": counts, "simulation": sim, "two_receiver_scope": two, "examples": examples,
           "gates": gates, "status": "PASS" if all(gates.values()) else "FAIL",
           "nonclaims": ["the CONJECTURE gate is exhaustive evidence in range, not a proof",
                         "the DP decider is checked against the definition, not proved in Lean"],
           "authority_effect": "NONE"}
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
