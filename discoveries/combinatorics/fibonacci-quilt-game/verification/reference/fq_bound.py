"""Fibonacci Quilt game: every game on n lasts at most (23/10) n + 2.95 moves.

Quilt numbers q_1..q_4 = 1, 2, 3, 4 and q_i = q_{i-2} + q_{i-3} (i >= 5). The
moves are those of Miller and Newlon (Fibonacci Quart. 58 (2020); arXiv
1909.01938), rules 1-5; rule 3(f) is read as q6,q6 -> q2,q8 or q5,q7 (the
printed "q3 and q7" does not preserve the value 14).

Potential: Phi = - sum over pieces of u(index), with u from fq_potential.json:
explicit rationals u_1..u_{J-1} (u_1 = 0) and u_i = alpha q_i - i/3 - beta for
i >= J. Every move except rule 2(a) lowers Phi by at least 1; rule 2(a) is used
at most once (Miller-Newlon Lemma 2.2). Start: Phi = -n u_1 = 0. End:
Phi >= -alpha n because u_i <= alpha q_i. So a game has at most
alpha n + 1 + max(0, Delta_2a) moves.

Gates (each required):
  * RULES_PRESERVE_VALUE: every rule instance (indices <= 60) preserves value;
  * POTENTIAL_EXACT: every rule instance with indices <= 200 lowers Phi by
    >= 1, in exact rational arithmetic;
  * TAIL_ANALYTIC: instances wholly in the closed-form region (indices >= J)
    reduce to the inequalities (i - 2)/3 + beta >= 1 (rule 1),
    (i - 1)/3 + beta >= 1 (rule 2b), 1 >= 1 (rule 3g), 4/3 >= 1 (rule 4e),
    which hold for i >= J; the q-terms cancel by q_{i+3} = q_i + q_{i+1},
    q_{i+5} = q_i + q_{i+4}, 2 q_i = q_{i-5} + q_{i+2},
    q_i + q_{i+3} = q_{i-5} + q_{i+4} (checked for i <= 200);
  * U_BELOW_ALPHA_Q: u_i <= alpha q_i for i <= 200 (and beta >= 0 beyond);
  * EXHAUSTIVE_n_le_40: the exhaustive longest game for n <= 40 is within the
    bound;
  * CONTROL: dropping the -i/3 term from the tail violates a constraint
    (rule 3(g) then changes the potential by 0).
"""
from __future__ import annotations
import json
import sys
from fractions import Fraction as Fr
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
q = [0, 1, 2, 3, 4]
while len(q) < 260:
    q.append(q[-3] + q[-2])


def instances(hi):
    R = []
    for i in range(1, hi + 1):
        R.append(("1", [i, i + 1], [3] if i == 1 else [i + 3]))
        if i >= 2:
            R.append(("2b", [i, i + 4], [i + 5]))
        if i == 1: R.append(("3", [1, 1], [2]))
        elif i == 2: R.append(("3", [2, 2], [4]))
        elif i == 3: R.append(("3", [3, 3], [2, 4]))
        elif i == 4: R += [("3", [4, 4], [1, 6]), ("3", [4, 4], [3, 5])]
        elif i == 5: R.append(("3", [5, 5], [1, 7]))
        elif i == 6: R += [("3", [6, 6], [2, 8]), ("3", [6, 6], [5, 7])]
        else: R.append(("3g", [i, i], [i - 5, i + 2]))
        if i in (1, 2): R.append(("4", [i, i + 3], [i + 4]))
        elif i == 3: R.append(("4", [3, 6], [1, 7]))
        elif i in (4, 5): R.append(("4", [i, i + 3], [1, i + 4]))
        elif i == 6: R.append(("4", [6, 9], [2, 10]))
        else: R.append(("4e", [i, i + 3], [i - 5, i + 4]))
    R.append(("5", [1, 3], [4]))
    return [t for t in R if max(t[1] + t[2]) <= hi]


def load():
    d = json.loads((HERE / "fq_potential.json").read_text())
    return Fr(d["alpha"]), d["J"], [Fr(x) for x in d["u"]], Fr(d["beta"])


def make_U(alpha, J, u, beta):
    def U(i):
        return u[i - 1] if i < J else alpha * q[i] - Fr(i, 3) - beta
    return U


def moves(c):
    out = []
    c = list(c)
    def mk(rem, add):
        d = c[:]
        for i in rem:
            d[i] -= 1
        if min(d) < 0:
            return
        for i in add:
            d[i] += 1
        out.append(tuple(d))
    for _, rem, add in instances(len(c) - 1):
        mk(rem, add)
    if not out and c[1] and c[5]:
        mk([1, 5], [2, 4])
    return out


@lru_cache(maxsize=None)
def longest(c):
    m = moves(c)
    return 0 if not m else 1 + max(longest(d) for d in m)


def main():
    alpha, J, u, beta = load()
    U = make_U(alpha, J, u, beta)
    inst = instances(200)
    value_ok = all(sum(q[i] for i in r) == sum(q[i] for i in a) for _, r, a in instances(60))
    pot_ok = all(sum(U(i) for i in a) - sum(U(i) for i in r) >= 1 for _, r, a in inst)
    tail_ok = (beta >= 0 and all(Fr(i - 2, 3) + beta >= 1 and Fr(i - 1, 3) + beta >= 1 for i in range(J, 201))
               and all(q[i + 3] == q[i] + q[i + 1] and q[i + 5] == q[i] + q[i + 4]
                       and 2 * q[i] == q[i - 5] + q[i + 2] and q[i] + q[i + 3] == q[i - 5] + q[i + 4]
                       for i in range(max(J - 9, 7), 200)))
    below_ok = all(U(i) <= alpha * q[i] for i in range(1, 201))
    d2a = U(1) + U(5) - U(2) - U(4)
    slack = 1 + max(Fr(0), d2a)
    ex = True
    worst = Fr(0)
    for n in range(1, 41):
        c = [0] * 22
        c[1] = n
        L = longest(tuple(c))
        if L > alpha * n + slack:
            ex = False
        worst = max(worst, Fr(L, n))
    def U2(i):          # control: drop the -i/3 term of the tail
        return u[i - 1] if i < J else alpha * q[i] - beta
    control = not all(sum(U2(i) for i in a) - sum(U2(i) for i in r) >= 1 for _, r, a in inst)
    gates = {
        "RULES_PRESERVE_VALUE": value_ok,
        "POTENTIAL_EXACT_indices_le_200": pot_ok,
        "TAIL_ANALYTIC": tail_ok,
        "U_BELOW_ALPHA_Q": below_ok,
        "EXHAUSTIVE_n_le_40": ex,
        "CONTROL_tail_without_index_term_fails": control,
    }
    out = {
        "schema": "cbmd.fq-game.bound.v1",
        "bound": "L <= %s n + %s" % (alpha, slack),
        "rule_2a_potential_increase": str(d2a),
        "max_ratio_n_le_40": float(worst),
        "gates": gates,
        "status": "PASS" if all(gates.values()) else "FAIL",
        "authority_effect": "NONE",
    }
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
