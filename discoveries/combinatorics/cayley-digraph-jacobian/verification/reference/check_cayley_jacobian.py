"""Jacobians of Cayley digraphs of finite abelian groups (Reiner's question): exact gates.

Setting: A finite abelian of order n, S a multiset of nonzero elements with sum 0 generating A,
G = Cay(A, S) (arcs g -> g + x).  Theorem (argument/WRITTEN_ARGUMENT.md): Jac(G) ~= A iff A is
cyclic and S = {a, -a}; |Jac(G)| > n otherwise, with |Jac| >= (3/2)^phi(n) n for cyclic A, s >= 3.

Gates (each required):
  * EXHAUSTIVE_SMALL: for all A with |A| <= 12 and |S| <= 4 (Smith normal form, exact), Jac ~= A
    exactly for the cyclic {a, -a} cases;
  * PRODUCT_FORMULA: n |Jac| = prod_{chi != 1} lambda_chi (Lemma 1), for all cases with |A| <= 10,
    |S| <= 4 (numerical product vs exact |Jac|, relative error < 1e-9);
  * ORBIT_NORMS: for cyclic A = Z_n (n <= 12, |S| <= 4): n |Jac| = prod_{d | n, d > 1} N(lambda_d)
    with exact resultant norms; p^2 | N(lambda_d) for d = p^k (Lemma 3); and for s >= 3
    N(lambda_n) >= (3/2)^phi(n) (p^2 if n = p^e) (Lemma 4);
  * NONCYCLIC_COUNT: for every noncyclic abelian p-group of order <= 64 (p = 2, 3) the number of
    nontrivial cyclic subgroups exceeds the exponent e = log_p |A_p| (brute force);
  * CONTROL: dropping the sum-zero hypothesis breaks the theorem: Cay(Z_3, {1}) (a directed
    3-cycle) has |Jac| = 1 < 3, and the surjection onto A fails;
  * EVIDENCE_SUMMARY: evidence/cayley_scans.json records no exception in the larger scans.
"""
from __future__ import annotations
import cmath
import itertools
import json
import os
import sys
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
EVIDENCE = os.path.normpath(os.path.join(HERE, '..', '..', 'evidence'))
from cayley_jac import abelian_groups, group_elements, generates, jac, invariant_factors_of_group  # noqa: E402


def cases(maxorder, maxsize):
    for order in range(2, maxorder + 1):
        for ds in abelian_groups(order):
            nz = [g for g in group_elements(ds) if any(g)]
            for size in range(2, maxsize + 1):
                for S in itertools.combinations_with_replacement(nz, size):
                    if any(sum(c) % d for c, d in zip(zip(*S), ds)):
                        continue
                    if not generates(S, ds):
                        continue
                    yield ds, S


def prod_list(xs):
    p = 1
    for x in xs:
        p *= x
    return p


def main():
    results = {}

    bad, tested, eq = [], 0, 0
    for ds, S in cases(12, 4):
        tested += 1
        J = sorted(jac(ds, S))
        if J == invariant_factors_of_group(ds):
            eq += 1
            if not (len(ds) == 1 and len(S) == 2):
                bad.append((ds, S))
    results['EXHAUSTIVE_SMALL'] = {'pass': not bad and tested > 0 and eq > 0, 'cases': tested,
                                   'jac_iso_A': eq, 'exceptions': bad}

    bad, tested = [], 0
    for ds, S in cases(10, 4):
        n = prod_list(ds)
        kappa = prod_list(jac(ds, S))
        P = 1
        for chi in itertools.product(*[range(d) for d in ds]):
            if not any(chi):
                continue
            z = sum(cmath.exp(2j * cmath.pi * sum(c * xi / d for c, xi, d in zip(chi, x, ds))) for x in S)
            P *= (len(S) - z)
        tested += 1
        if abs(P.real - n * kappa) > 1e-9 * n * kappa or abs(P.imag) > 1e-6 * n * kappa:
            bad.append((ds, S))
    results['PRODUCT_FORMULA'] = {'pass': not bad and tested > 0, 'cases': tested, 'failures': bad[:5]}

    from sympy import cyclotomic_poly, resultant, symbols, divisors, factorint, totient
    zz = symbols('z')

    def norm(d, S):
        f = sum(1 - zz ** (x % d) for x in S)
        return abs(int(resultant(cyclotomic_poly(d, zz), f, zz)))
    bad, tested = [], 0
    for n in range(2, 13):
        for s in range(2, 5):
            for S in itertools.combinations_with_replacement(range(1, n), s):
                if sum(S) % n:
                    continue
                g = 0
                for x in S:
                    g = gcd(g, x)
                if gcd(g, n) != 1:
                    continue
                kappa = prod_list(jac((n,), [(x,) for x in S]))
                total = 1
                ok = True
                for d in divisors(n)[1:]:
                    Nd = norm(d, S)
                    total *= Nd
                    f = factorint(d)
                    if len(f) == 1 and Nd % (list(f)[0] ** 2):
                        ok = False
                if total != n * kappa:
                    ok = False
                if s >= 3:
                    f = factorint(n)
                    base = list(f)[0] ** 2 if len(f) == 1 else 1
                    if norm(n, S) < (1.5 ** int(totient(n))) * base * (1 - 1e-12):
                        ok = False
                tested += 1
                if not ok:
                    bad.append((n, S))
    results['ORBIT_NORMS'] = {'pass': not bad and tested > 0, 'cases': tested, 'failures': bad[:5]}

    bad, tested = [], 0
    for p in (2, 3):
        for order_exp in range(2, 7 if p == 2 else 4):
            for ds in abelian_groups(p ** order_exp):
                if len(ds) < 2:
                    continue
                elems = group_elements(ds)
                cyc = set()
                for g in elems:
                    if not any(g):
                        continue
                    sub = {tuple([0] * len(ds))}
                    x = g
                    while x not in sub:
                        sub.add(x)
                        x = tuple((a + b) % d for a, b, d in zip(x, g, ds))
                    cyc.add(frozenset(sub))
                tested += 1
                if not len(cyc) > order_exp:
                    bad.append(ds)
    results['NONCYCLIC_COUNT'] = {'pass': not bad and tested > 0, 'groups': tested, 'failures': bad}

    # control: without sum zero, Cay(Z_3,{1}) is a directed 3-cycle with one arborescence
    kappa = prod_list(jac((3,), [(1,)]))
    results['CONTROL'] = {'pass': kappa == 1, 'jac_order_Z3_S1': kappa}

    ev = json.load(open(os.path.join(EVIDENCE, 'cayley_scans.json')))
    ok = all(r['exceptions'] == 0 for r in ev['scans']) and ev['bound_check']['failures'] == 0 \
        and ev['norm_check']['failures'] == 0
    results['EVIDENCE_SUMMARY'] = {'pass': ok}

    allp = all(v['pass'] for v in results.values())
    for k, v in results.items():
        print(k, 'PASS' if v['pass'] else 'FAIL')
    if '--write' in sys.argv:
        with open(os.path.join(EVIDENCE, 'check_cayley_jacobian.json'), 'w') as fh:
            json.dump({'schema': 'cbmd.cayley-jacobian.check.v1', 'gates': results, 'pass': allp}, fh, indent=1, default=str)
            fh.write('\n')
    print('ALL PASS' if allp else 'FAILURES')
    return 0 if allp else 1


if __name__ == '__main__':
    sys.exit(main())
