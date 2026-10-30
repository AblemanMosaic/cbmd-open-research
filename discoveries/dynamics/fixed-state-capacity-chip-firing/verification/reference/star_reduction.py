"""The star reduction against exact simulation.

The Lean development (`Star.lean`, `Bins.lean`) proves, for a star with senders
holding bundles a_i and a receiver of capacity and outdegree B:

  reach_iff                          reachable states = bin runs
  all_fired_reachable_iff            all-fired state reachable  <=> some order of
                                     all bundles is a bin run ending at fill r
  normal_form_reachable_iff_partition  (r = 0) <=> the bundles partition into
                                     groups of total exactly B
  bad_terminal_reachable_iff         a bad terminal state is reachable <=> some
                                     bin run gets stuck

This script checks the two decision predicates those theorems name against the
weighted dossier's exact simulator (`characterize.cap_terminals`, which explores
every capacity-legal firing order), on random stars:

  * GOOD: the ordinary normal form is capacity-reachable  <=>  an exact-bin
    order of the bundles exists (search over bin runs, written from the Lean
    definition of `Run`);
  * BAD: a reachable capacity-terminal state that is not ordinarily stable
    exists  <=>  some bin run gets stuck.

Gates (each required):
  * both predicates agree with simulation on every instance;
  * BRIDGE: the ordinary normal form is the all-fired state with total mod B at
    the receiver, as the Lean target assumes;
  * CONSISTENCY with the weighted transfer theorem: every instance meeting its
    bound (all bundles of size 1, so C(v) = B >= d(v) + max a - 1) is GOOD and
    not BAD; the instances below the bound carry all the variety;
  * the three possible (GOOD, BAD) combinations occur, including both together
    (order dependence); (not GOOD, not BAD) is impossible because capacity
    firing terminates, and must not occur;
  * CONTROL: a run rule that lets a bundle cross a multiple of B (fill mod B)
    must disagree with simulation somewhere, or the GOOD gate is idle.
"""
from __future__ import annotations

import json
import random
import sys
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
WEIGHTED = HERE.parents[2] / "weighted-capacity-chip-firing" / "verification" / "reference"
sys.path.insert(0, str(WEIGHTED))
from characterize import cap_terminals, ordinary_normal  # noqa: E402


def star(a, B):
    k = len(a)
    n = k + 1
    A = [[0] * n for _ in range(n)]
    for i in range(k):
        A[i][k] = a[i]
    s = [0] * k + [B]
    c = list(a) + [B]
    return A, s, c, n, tuple(a) + (0,)


def runs(a, B, crossing=False):
    """All (fired-set, fill) pairs reachable by bin runs, from the Lean `Run`."""
    k = len(a)
    seen = set()
    stack = [(frozenset(), 0)]
    while stack:
        L, f = stack.pop()
        if (L, f) in seen:
            continue
        seen.add((L, f))
        if f == B:
            stack.append((L, 0))
        for i in range(k):
            if i in L:
                continue
            if f + a[i] <= B:
                stack.append((L | {i}, f + a[i]))
            elif crossing:
                stack.append((L | {i}, (f + a[i]) % B))
    return seen


def good_pred(a, B, crossing=False):
    allL = frozenset(range(len(a)))
    return any(L == allL and f == sum(a) % B for L, f in runs(a, B, crossing))


def bad_pred(a, B):
    k = len(a)
    for L, f in runs(a, B):
        rest = [i for i in range(k) if i not in L]
        if f < B and rest and all(f + a[i] > B for i in rest):
            return True
    return False


def run(trials=3000, seed=2):
    rng = random.Random(seed)
    seen = set()
    agree_good = agree_bad = bridge = below_bound = mutant = 0
    above_bound = above_bound_good = 0
    combos = {(g, b): 0 for g in (False, True) for b in (False, True)}
    for _ in range(trials):
        B = rng.randint(2, 9)
        k = rng.randint(1, 6)
        a = [rng.randint(1, B) for _ in range(k)]
        if rng.random() < 0.7:
            r = (-sum(a)) % B
            if r:
                a.append(r)
        key = (tuple(sorted(a)), B)
        if key in seen:
            continue
        seen.add(key)
        A, s, c, n, x = star(a, B)
        onf = ordinary_normal(A, s, n, x)
        T = cap_terminals(A, s, c, n, x)
        sim_good = onf in T
        sim_bad = any(t != onf for t in T)
        g, b = good_pred(a, B), bad_pred(a, B)
        agree_good += g == sim_good
        agree_bad += b == sim_bad
        bridge += onf == tuple([0] * len(a)) + (sum(a) % B,)
        below = c[-1] < B + max(a) - 1
        below_bound += below
        if not below:
            above_bound += 1
            above_bound_good += sim_good and not sim_bad
        mutant += good_pred(a, B, crossing=True) != sim_good
        combos[(sim_good, sim_bad)] += 1
    N = len(seen)
    gates = {
        "good_predicate_exact": agree_good == N,
        "bad_predicate_exact": agree_bad == N,
        "normal_form_is_all_fired_state": bridge == N,
        "consistent_with_weighted_theorem": above_bound > 0 and above_bound_good == above_bound,
        "three_possible_combinations_occur": all(combos[c] > 0 for c in
                                                 [(True, False), (True, True), (False, True)]),
        "impossible_combination_absent": combos[(False, False)] == 0,
        "control_crossing_rule_disagrees": mutant > 0,
    }
    return {"schema": "cbmd.fixed-state-star-reduction.v1", "instances": N,
            "good_agree": agree_good, "bad_agree": agree_bad,
            "normal_form_bridge": bridge, "below_weighted_bound": below_bound,
            "at_or_above_bound": above_bound, "at_or_above_bound_good": above_bound_good,
            "combinations_good_bad": {f"{g}/{b}": v for (g, b), v in combos.items()},
            "crossing_control_disagreements": mutant, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["checks the compiled correspondence on random stars; the NP-hardness of 3-PARTITION is classical and cited, not proved"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 3000)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
