"""Finite regions left by the analytic bounds of Theorems 7 and 9 (n = 3), recomputed by brute force.

Each inequality is a NECESSARY condition for minimality derived in argument/WRITTEN_ARGUMENT.md;
this script lists the parameter values satisfying it (logarithms, exact integer constraints) and
checks that they lie inside the region covered by the finite computations:
  type C, f = 1:  m^6 (3/2)^(|A| - 3m + 2) <= |A|^3,   m^2 | |A|            ->  (m,|A|) in {(1,<=24),(2,4|8|12)}
  type C, f = 3:  m^6 (3/2)^(|A| - 3m + 2) <= |A|^3 / 3^15, 3 | |A|          ->  none
  type D, f = 1:  m e 2^e (3/2)^((|A| - 3m + 2)/6) <= 4|A|, e >= m           ->  m = 1: |A| <= 75; m = 2: |A| <= 36
  type D, f = 3:  sqrt(27) m e 2^e (3/2)^((|A| - 3m + 2)/6) 27 <= 36 |A|, e >= max(m, 3)  ->  none
  type B, exceptional:  |1 - (-2)^z| <= 3 |Gbar| |Gbar^ab|                     ->  z <= 6 (A4), 7 (S4, A5)
  type B, dihedral, C~ not in SL2:  |1-(-2)^z| m^4 m'^2 (3/2)^(c - 2m - m' + 2) <= 48 c^2,
                   m^2 | c, m m' | c, z | c, m' <= c/2                          ->  c <= 23
The searches run to |A|, c <= 4000 (beyond which each left side exceeds the right side by a margin
that only grows; see the written argument for the asymptotic step).
"""
from math import log, sqrt
import sys

L15 = log(1.5)
NMAX = 4000


def type_c(f):
    sols = []
    for n in range(1, NMAX + 1):
        if f == 3 and n % 3:
            continue
        for m in range(1, int(sqrt(n)) + 1):
            if n % (m * m):
                continue
            lhs = 6 * log(m) + (n - 3 * m + 2) * L15
            rhs = 3 * log(n) - (15 * log(3) if f == 3 else 0)
            if lhs <= rhs + 1e-12:
                sols.append((m, n))
    return sols


def type_d(f):
    sols = []
    for n in range(1, NMAX + 1):
        if f == 3 and n % 3:
            continue
        for m in range(1, int(sqrt(n)) + 1):
            if n % (m * m):
                continue
            e = max(m, 3) if f == 3 else m       # e |-> e 2^e is increasing; use the least admissible e
            if f == 1:
                lhs = log(m) + log(e) + e * log(2) + (n - 3 * m + 2) / 6 * L15
                rhs = log(4 * n)
            else:
                lhs = 0.5 * log(27) + log(27) + log(m) + log(e) + e * log(2) + (n - 3 * m + 2) / 6 * L15
                rhs = log(36 * n)
            if lhs <= rhs + 1e-12:
                sols.append((m, n))
    return sols


def type_b_exceptional():
    out = {}
    for name, order, ab in (('A4', 12, 3), ('S4', 24, 2), ('A5', 60, 1)):
        out[name] = max(z for z in range(1, 64) if abs(1 - (-2) ** z) <= 3 * order * ab)
    return out


def divisors(x):
    return [d for d in range(1, x + 1) if x % d == 0]


def type_b_dihedral():
    best = 0
    for c in range(1, NMAX + 1):
        dc = divisors(c)
        for m in range(1, int(sqrt(c)) + 1):
            if c % (m * m):
                continue
            for mp in divisors(c // m):
                if mp > c // 2:
                    continue
                for z in dc:
                    if z > 64:
                        break
                    lhs = log(abs(1 - (-2) ** z)) + 4 * log(m) + 2 * log(mp) + (c - 2 * m - mp + 2) * L15
                    if lhs <= log(48 * c * c) + 1e-12:
                        best = max(best, c)
    return best


def main():
    res = {}
    c1 = type_c(1)
    res['typeC_f1'] = {'solutions': c1, 'ok': all((m == 1 and n <= 24) or (m == 2 and n in (4, 8, 12)) for m, n in c1)}
    c3 = type_c(3)
    res['typeC_f3'] = {'solutions': c3, 'ok': c3 == []}
    d1 = type_d(1)
    res['typeD_f1'] = {'max_by_m': {m: max(n for mm, n in d1 if mm == m) for m in sorted({mm for mm, _ in d1})},
                       'ok': all((m == 1 and n <= 75) or (m == 2 and n <= 36) for m, n in d1)}
    d3 = type_d(3)
    res['typeD_f3'] = {'solutions': d3, 'ok': d3 == []}
    ex = type_b_exceptional()
    res['typeB_exceptional_zmax'] = {'zmax': ex, 'ok': ex == {'A4': 6, 'S4': 7, 'A5': 7}}
    bd = type_b_dihedral() if '--quick' not in sys.argv else None
    res['typeB_dihedral_cmax'] = {'cmax': bd, 'ok': bd is None or bd <= 23}
    for k, v in res.items():
        print(k, 'OK' if v['ok'] else 'FAIL', {kk: vv for kk, vv in v.items() if kk not in ('ok', 'solutions')})
    allok = all(v['ok'] for v in res.values())
    print('ALL OK' if allok else 'FAILURES')
    return res, allok


if __name__ == '__main__':
    sys.exit(0 if main()[1] else 1)
