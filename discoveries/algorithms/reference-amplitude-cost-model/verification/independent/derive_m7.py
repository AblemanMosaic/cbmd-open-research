"""A standalone derivation check of the master formula B5-M7.

The cost theorem compares the frozen enumeration producer `literal_numerator`
against the closed formula

    n(A,R,delta,f) = 2^(R-1) (-1)^A  sum_{k=0}^{d} C(N,k) C(A+d-k-1, d-k),
    d = R-1-f,  N = A+R-delta,

which it calls "the proved identity B5-M7".  The identity is compiled in this
repository's native package (`entry_eq_masterNumerator`, about the native
`LayoutNumerator.entry`).  `argument/M7_DERIVATION.md` derives it again against
the PYTHON producer the cost theorem measures, along the native proof's route,
and this script checks each step separately.  Steps 1-4 are checked with code written
here from the definitions -- NOTHING is imported from `reference-model/src`
until the final, separately labelled cross-check.

  S1  indicator collapse:  for B within the active set,
          [swap(base,B) = y]  =  [B n D = E \\ {t}]
  S2  inner-sum collapse:  n = (-1)^f sum_i c_{f+i} 2^(d-i) C(delta-1-f, i)
  S3  parity coefficients: c_j = (-1)^A (-2)^j sum_{m<R-j} 2^m C(A+m-1, m)
  S4  binomial identity, by the substitution x = z/(1+z):
          [x^d] (1-x)^(delta-R-1+d) (1-2x)^(-A) = [z^d] (1+z)^N (1-z)^(-A)

Gates: each step exact on its box; both indicator values occur; nonzero
amplitudes occur; and two mutated statements (N off by one in the master
formula; t not removed from E in S1) must FAIL, or the checks are idle.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction
from itertools import combinations, product
from math import comb as _comb


def comb(n, k):
    """Generalised binomial, valid for negative n."""
    if k < 0:
        return 0
    if n < 0:
        return (-1) ** k * _comb(-n + k - 1, k)
    return _comb(n, k) if k <= n else 0


def swap(u, S, Q):
    a = list(u)
    for p in S:
        a[p], a[Q + p] = a[Q + p], a[p]
    return tuple(a)


# ---------------------------------------------------------------- S1
def check_indicator(Qmax=5, alphabet=2, mutate=False):
    cases = mism = ones = 0
    for Q in range(1, Qmax + 1):
        for u in product(range(alphabet), repeat=2 * Q):
            D = {p for p in range(Q) if u[p] != u[Q + p]}
            for M in product([0, 1], repeat=Q):
                y = swap(u, [p for p in range(Q) if M[p]], Q)
                E = {p for p in range(Q) if y[p] != u[Q + p]}
                for t in sorted(E):
                    active = [p for p in range(Q) if p != t]
                    base = swap(u, active, Q)
                    target = E if mutate else E - {t}
                    for k in range(len(active) + 1):
                        for B in combinations(active, k):
                            lhs = swap(base, B, Q) == y
                            rhs = (set(B) & D) == target
                            cases += 1
                            ones += lhs
                            mism += lhs != rhs
    return {"cases": cases, "mismatches": mism, "indicator_true": ones}


# ---------------------------------------------------------------- S3
def parity_solve(A, R):
    """Own exact solve of sum_j C(A+i,j) c_j = (-1)^(A+i), i < R."""
    M = [[Fraction(comb(A + i, j)) for j in range(R)] + [Fraction((-1) ** (A + i))]
         for i in range(R)]
    for col in range(R):
        piv = next(r for r in range(col, R) if M[r][col] != 0)
        M[col], M[piv] = M[piv], M[col]
        M[col] = [x / M[col][col] for x in M[col]]
        for r in range(R):
            if r != col and M[r][col] != 0:
                f = M[r][col]
                M[r] = [a - f * b for a, b in zip(M[r], M[col])]
    return [M[r][R] for r in range(R)]


def c_closed(A, R):
    return [(-1) ** A * (-2) ** j * sum(2 ** m * comb(A + m - 1, m) for m in range(R - j))
            for j in range(R)]


def check_parity(Amax=6, Rmax=7):
    cases = mism = 0
    for A in range(Amax + 1):
        for R in range(1, Rmax + 1):
            cases += 1
            mism += [Fraction(x) for x in c_closed(A, R)] != parity_solve(A, R)
    return {"cases": cases, "mismatches": mism}


# ---------------------------------------------------------------- S2
def numerator_by_definition(u, y, t, A, R):
    """The producer's definition, rewritten here: base = u swapped on the
    active set; sum over S of size j < R and B within S."""
    Q = len(u) // 2
    active = [p for p in range(Q) if p != t]
    base = swap(u, active, Q)
    c = c_closed(A, R)
    n = 0
    for j in range(R):
        for S in combinations(active, j):
            d = sum((-1) ** k * (swap(base, B, Q) == y)
                    for k in range(j + 1) for B in combinations(S, k))
            n += c[j] * 2 ** (R - 1 - j) * d
    return n


def n_inner(A, R, delta, f):
    d = R - 1 - f
    c = c_closed(A, R)
    return (-1) ** f * sum(c[f + i] * 2 ** (d - i) * comb(delta - 1 - f, i) for i in range(d + 1))


def check_inner(Qmax=5, Amax=3, Rmax=4):
    cases = mism = nonzero = 0
    for Q in range(1, Qmax + 1):
        for u in product([0, 1], repeat=2 * Q):
            D = [p for p in range(Q) if u[p] != u[Q + p]]
            for M in product([0, 1], repeat=Q):
                y = swap(u, [p for p in range(Q) if M[p]], Q)
                E = [p for p in range(Q) if y[p] != u[Q + p]]
                if not E:
                    continue
                t = E[0]
                for A in range(Amax + 1):
                    for R in range(1, Rmax + 1):
                        if len(E) > R:
                            continue
                        lhs = numerator_by_definition(u, y, t, A, R)
                        rhs = n_inner(A, R, len(D), len(E) - 1)
                        cases += 1
                        nonzero += lhs != 0
                        mism += lhs != rhs
    return {"cases": cases, "mismatches": mism, "nonzero": nonzero}


# ---------------------------------------------------------------- S4
def master(A, R, delta, f, shift=0):
    d = R - 1 - f
    N = A + R - delta + shift
    return 2 ** (R - 1) * (-1) ** A * sum(comb(N, k) * comb(A + d - k - 1, d - k)
                                          for k in range(d + 1))


def check_identity(Amax=8, Rmax=8, Dmax=12):
    cases = mism = mutant = 0
    for A in range(Amax + 1):
        for R in range(1, Rmax + 1):
            for delta in range(1, Dmax + 1):
                for f in range(min(R, delta)):
                    cases += 1
                    v = n_inner(A, R, delta, f)
                    mism += v != master(A, R, delta, f)
                    mutant += v != master(A, R, delta, f, shift=1)
    return {"cases": cases, "mismatches": mism, "mutated_master_mismatches": mutant}


# ------------------------------------------------- cross-check vs source
def check_against_source(Qmax=5, Amax=3, Rmax=4):
    src = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "reference-model", "src")
    sys.path.insert(0, src)
    from owner_sum import Meter, literal_numerator  # noqa: E402
    cases = mism = 0
    for Q in range(1, Qmax + 1):
        for u in product([0, 1], repeat=2 * Q):
            D = [p for p in range(Q) if u[p] != u[Q + p]]
            for M in product([0, 1], repeat=Q):
                y = swap(u, [p for p in range(Q) if M[p]], Q)
                E = [p for p in range(Q) if y[p] != u[Q + p]]
                if not E:
                    continue
                for A in range(Amax + 1):
                    for R in range(len(E), Rmax + 1):
                        cases += 1
                        mism += literal_numerator(u, y, E[0], A, R, Meter()) != \
                            master(A, R, len(D), len(E) - 1)
    return {"cases": cases, "mismatches": mism}


def run():
    s1 = check_indicator()
    s1_r3 = check_indicator(Qmax=3, alphabet=3)
    s1_mut = check_indicator(Qmax=4, mutate=True)
    s2 = check_inner()
    s3 = check_parity()
    s4 = check_identity()
    src = check_against_source()
    gates = {
        "S1_indicator_collapse_exact": s1["mismatches"] == 0 and s1_r3["mismatches"] == 0,
        "S1_both_indicator_values_occur": 0 < s1["indicator_true"] < s1["cases"],
        "S1_mutation_detected": s1_mut["mismatches"] > 0,
        "S2_inner_sum_exact": s2["mismatches"] == 0 and s2["cases"] > 0,
        "S2_nonzero_amplitudes_occur": s2["nonzero"] > 0,
        "S3_parity_closed_form_exact": s3["mismatches"] == 0,
        "S4_identity_exact": s4["mismatches"] == 0,
        "S4_mutation_detected": s4["mutated_master_mismatches"] > 0,
        "cross_check_against_frozen_source": src["mismatches"] == 0 and src["cases"] > 0,
    }
    return {"schema": "cbmd.amplitude-m7-derivation.v1",
            "S1_indicator": s1, "S1_indicator_alphabet3": s1_r3, "S1_mutated": s1_mut,
            "S2_inner_sum": s2, "S3_parity": s3, "S4_identity": s4,
            "cross_check_source": src, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": [
                "written proof checked step by step on finite boxes; not compiled",
                "separately written in this repository, not externally authored; external mathematical review remains open",
                "the derivation assumes y lies in the swap orbit of u and t is in E(y), the conditions under which the cost theorem invokes the producer",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run()
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
