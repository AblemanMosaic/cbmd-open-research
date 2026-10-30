"""Combine Smallest: the counter lemma, the pile cycle, and the length constant.

Indexing F_1 = 1, F_2 = 2, F_{k+1} = F_k + F_{k-1} (so F_0 = 1). Combine Smallest
(CS) moves, in priority order: add two 1's; add the smallest consecutive pair
F_{j-1}, F_j -> F_{j+1}; split the smallest duplicate F_j, F_j -> F_{j+1}, F_{j-2}
(F_2, F_2 -> F_3, F_1).

A configuration on indices <= s is *normal* if it has no duplicate and no two
consecutive pieces. The unit-fed counter Q_s receives one piece at index s at a
time; CS then runs, and a piece reaching index s + 1 is removed (a carry).

Gates (each required):
  * COUNTER_TRANSITIONS: for 1 <= s <= 14 and every normal state, one feed of
    Q_s, simulated directly under CS, agrees with the recursive A/B/C model of
    the written argument (new state, moves, splits, carry);
  * COUNTER_CYCLE: for 1 <= s <= 18, F_{s+1} feeds from the empty state make
    F_{s+1} - 1 moves (F_s - 1 of them splits) and F_s carries, visit every
    normal state on indices <= s once, and return to empty;
  * PILE_CYCLE: a lone pile at index i (2 <= i <= 10) of F_{i+2} t pieces:
    each extra F_{i+2} pieces cost exactly F_{i+2} - 1 moves (F_i - 1 splits)
    and yield F_i pieces at index i + 2;
  * TAIL_CASES: for even P in 4..14, every normal counter state on indices
    <= P - 2, pile p in 0..6 at P and q in 6..9 pieces at P + 2, CS reaches a
    first split at index P + 2 in the standard level form (normal on <= P,
    nothing at P + 1 or P + 3, at most 2 pieces at P + 4, nothing above);
  * LEVEL_START: in the full CS game for every n in range, each first split at
    a new top index P with at least 5 pieces there happens at even P in the
    standard level form;
  * BUDGET_ERROR: |F_{i+2} - phi^2 F_i| <= 1 for i <= 90 (used in the budget
    lemma);
  * CONSTANT: 1/2 + sum_{j>=1} (1/F_{2j})(1 - 1/F_{2j+2}) equals
    sum_{k>=1} 1/Fib(2k-1) - 1/phi (standard Fibonacci) and the split-count form
    1 + sum_{j>=1} (1/F_{2j+2} - 1/(F_{2j} F_{2j+2})), to 45 digits;
  * LENGTH: |L_CS(n) - c n| <= (log_phi n + 3)^2 for every n in range (the
    proved error is O(log^2 n) with an unstated constant; this is a sanity
    bound, and the observed deviations are far smaller);
  * CONTROL: a mutated counter model (state C costing two moves) disagrees
    with direct simulation.
"""
from __future__ import annotations

import json
import math
import sys
from decimal import Decimal, getcontext

N_MAX = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 3000

F = [1, 1, 2]  # F[0] = 1, F[1] = 1, F[2] = 2: game indexing F_k = F[k] for k >= 1
while len(F) < 420:
    F.append(F[-1] + F[-2])


def cs_step(c):
    """One CS move on counts c[1..]; c[0] unused. Returns (kind, index) or None."""
    if c[1] >= 2:
        c[1] -= 2
        c[2] += 1
        return ("add", 2)
    top = len(c) - 2
    for j in range(2, top + 1):
        if c[j - 1] and c[j]:
            c[j - 1] -= 1
            c[j] -= 1
            c[j + 1] += 1
            return ("add", j + 1)
    for j in range(2, top + 1):
        if c[j] >= 2:
            c[j] -= 2
            c[j + 1] += 1
            c[j - 2 if j >= 3 else 1] += 1
            return ("split", j)
    return None


def normal(c, lo, hi):
    return all(c[j] <= 1 for j in range(lo, hi + 1)) and all(
        not (c[j] and c[j + 1]) for j in range(lo, hi))


def normal_states(s):
    """All normal configurations on indices 1..s, as tuples of length s."""
    out = [()]
    for _ in range(s):
        out = [t + (0,) for t in out] + [t + (1,) for t in out if not t or t[-1] == 0]
    return out


def feed_direct(s, state):
    """Feed Q_s once by direct CS simulation; return (state, moves, splits, carry)."""
    c = [0] * (s + 6)
    for j, x in enumerate(state, start=1):
        c[j] = x
    c[s] += 1
    moves = splits = carry = 0
    while True:
        if c[s + 1]:
            carry += c[s + 1]
            c[s + 1] = 0
        mv = cs_step(c)
        if mv is None:
            break
        moves += 1
        splits += mv[0] == "split"
        if any(c[s + 2:]):
            raise AssertionError("piece escaped above s + 1")
    if c[s + 1]:
        carry += c[s + 1]
        c[s + 1] = 0
    return tuple(c[1:s + 1]), moves, splits, carry


def feed_model(s, state, c_cost=1):
    """The recursive A/B/C model of the written argument."""
    st = list(state)
    if s == 1:
        if st[0] == 0:
            return (1,), 0, 0, 0
        return (0,), 1, 0, 1
    if s == 2:
        if st == [0, 0]:
            return (0, 1), 0, 0, 0
        if st == [0, 1]:
            return (1, 0), 1, 1, 1
        return (0, 0), 1, 0, 1  # (1, 0): add (1, 2) -> 3
    top, below = st[s - 1], st[s - 2]
    if top == 0 and below == 0:  # A
        st[s - 1] = 1
        return tuple(st), 0, 0, 0
    if top == 1:  # B: split at s -> carry at s + 1, feed Q_{s-2} at s - 2
        sub, mv, sp, cr = feed_model(s - 2, tuple(st[:s - 2]), c_cost)
        new = list(sub) + [1 if cr else 0, 0]
        return tuple(new), 1 + mv, 1 + sp, 1
    # C: piece at s - 1, feed at s -> add (s - 1, s) -> carry
    st[s - 2] = 0
    return tuple(st), c_cost, 0, 1


def counter_transitions(max_s=14, c_cost=1):
    for s in range(1, max_s + 1):
        for state in normal_states(s):
            if feed_direct(s, state) != feed_model(s, state, c_cost):
                return False
    return True


def counter_cycle(max_s=18):
    for s in range(1, max_s + 1):
        state = tuple([0] * s)
        moves = splits = carries = 0
        seen = set()
        for _ in range(F[s + 1]):
            state, mv, sp, cr = feed_model(s, state)
            moves += mv
            splits += sp
            carries += cr
            seen.add(state)
        if not (moves == F[s + 1] - 1 and splits == F[s] - 1 and carries == F[s]
                and not any(state) and len(seen) == F[s + 1] == len(normal_states(s))):
            return False
    return True


def pile_run(i, m):
    c = [0] * (i + 10)
    c[i] = m
    moves = splits = 0
    while c[i] >= 2 or any(c[j] >= 2 for j in range(1, i)) or any(
            c[j] and c[j + 1] for j in range(1, i + 1)):
        mv = cs_step(c)
        if mv is None:
            break
        moves += 1
        splits += mv[0] == "split"
    return moves, splits, c[i + 2]


def pile_cycle(max_i=10, reps=5):
    for i in range(2, max_i + 1):
        runs = [pile_run(i, F[i + 2] * t) for t in range(1, reps + 1)]
        for a, b in zip(runs, runs[1:]):
            if (b[0] - a[0], b[1] - a[1], b[2] - a[2]) != (F[i + 2] - 1, F[i] - 1, F[i]):
                return False
    return True


def standard_level(c, P):
    """Standard form at the first split of level P (pile at P)."""
    if P == 2:
        return c[1] <= 1 and c[3] == 0 and not any(c[5:])
    return (normal(c, 1, P - 2) and c[P - 1] == 0 and c[P + 1] == 0
            and c[P + 3] == 0 and c[P + 2] <= 2 and not any(c[P + 4:]))


def tail_cases(Ps=range(4, 15, 2)):
    for P in Ps:
        for state in normal_states(P - 2):
            for p in range(0, 7):
                for q in range(6, 10):
                    c = [0] * (P + 12)
                    for j, x in enumerate(state, start=1):
                        c[j] = x
                    c[P] = p
                    c[P + 2] = q
                    while True:
                        # the next move is a split at index >= P + 2: stop there
                        probe = c[:]
                        mv = cs_step(probe)
                        if mv is None:
                            return False  # q >= 6 forces a further split
                        if mv[0] == "split" and mv[1] >= P + 2:
                            if mv[1] != P + 2 or not standard_level(c, P + 2):
                                return False
                            break
                        c = probe
    return True


def level_starts(n):
    c = [0] * 100
    c[1] = n
    top = 0
    out = []
    while True:
        probe = c[:]
        mv = cs_step(probe)
        if mv is None:
            return out
        if mv[0] == "split" and mv[1] > top:
            top = mv[1]
            out.append((top, c[:]))
        c = probe


def level_start_check(n_max):
    for n in range(1, n_max + 1):
        for P, c in level_starts(n):
            if c[P] >= 5 and (P % 2 or not standard_level(c, P)):
                return False
    return True


def cs_length(n):
    c = [0] * 100
    c[1] = n
    L = 0
    while cs_step(c) is not None:
        L += 1
    return L


def constants():
    getcontext().prec = 80
    D = Decimal
    phi = (1 + D(5).sqrt()) / 2
    series = D(1) / 2 + sum((1 / D(F[2 * j])) * (1 - 1 / D(F[2 * j + 2])) for j in range(1, 200))
    fib = [0, 1]
    while len(fib) < 820:
        fib.append(fib[-1] + fib[-2])
    odd = sum(1 / D(fib[2 * k - 1]) for k in range(1, 400))
    closed = odd - 1 / phi
    split_form = 1 + sum(1 / D(F[2 * j + 2]) - 1 / (D(F[2 * j]) * D(F[2 * j + 2]))
                         for j in range(1, 200))
    tol = D(10) ** -45
    ok = abs(series - closed) < tol and abs(series - split_form) < tol
    budget = all(abs(D(F[i + 2]) - phi * phi * D(F[i])) <= 1 for i in range(1, 91))
    return ok, budget, series


def main():
    const_ok, budget_ok, c = constants()
    cf = float(c)
    phi = (1 + 5 ** 0.5) / 2
    worst = 0.0
    length_ok = True
    devs = []
    for n in range(2, N_MAX + 1):
        d = cs_length(n) - cf * n
        devs.append(d)
        if abs(d) > (math.log(n, phi) + 3) ** 2:
            length_ok = False
        worst = max(worst, abs(d))
    gates = {
        "COUNTER_TRANSITIONS_direct_equals_model_s_le_14": counter_transitions(),
        "COUNTER_CYCLE_s_le_18": counter_cycle(),
        "PILE_CYCLE_i_le_10": pile_cycle(),
        "TAIL_CASES_even_P_4_to_14": tail_cases(),
        "LEVEL_START_standard_form": level_start_check(min(N_MAX, 3000)),
        "BUDGET_ERROR_bound": budget_ok,
        "CONSTANT_three_forms_agree": const_ok,
        "LENGTH_within_log_squared": length_ok,
        "CONTROL_mutated_counter_model_fails": not counter_transitions(8, c_cost=2),
    }
    out = {
        "schema": "cbmd.deterministic-zeckendorf.cs-constant.v1",
        "n_max": N_MAX,
        "constant": str(c)[:47],
        "max_abs_deviation_L_minus_cn": round(worst, 6),
        "min_deviation": round(min(devs), 6),
        "max_deviation": round(max(devs), 6),
        "gates": gates,
        "status": "PASS" if all(gates.values()) else "FAIL",
        "nonclaims": [
            "the asymptotic L_CS(n) = c n + O(log^2 n) is a written proof, not machine-checked",
            "boundedness of L_CS(n) - c n is not claimed",
        ],
        "authority_effect": "NONE",
    }
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
