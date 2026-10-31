"""Sector lemma (Lemma 2): for U in SU(n), z = n - tr U is 0 or |arg z| <= pi/2 - pi/n.

Checks (n = 2..10): (i) the edge inequality sum cos(theta_j - pi/n) <= n cos(pi/n) on 200000 random
points of the maximal torus (sum theta_j = 0) plus all points with angles in (2 pi / 60) Z summing to
0 mod 2 pi for n <= 4; (ii) the bound is attained by zeta_n I.  Deterministic (seeded)."""
import itertools, math, sys
import numpy as np


def main():
    rng = np.random.default_rng(20261031)
    ok = True
    for n in range(2, 11):
        th = rng.uniform(-math.pi, math.pi, (200000, n - 1))
        th = np.concatenate([th, -th.sum(axis=1, keepdims=True)], axis=1)
        lhs = np.cos(th - math.pi / n).sum(axis=1)
        worst = float(lhs.max() - n * math.cos(math.pi / n))
        if n <= 4:
            grid = [2 * math.pi * k / 60 for k in range(60)]
            for t in itertools.product(grid, repeat=n - 1):
                last = -sum(t)
                v = sum(math.cos(x - math.pi / n) for x in t + (last,))
                worst = max(worst, v - n * math.cos(math.pi / n))
        z = n - n * complex(math.cos(2 * math.pi / n), math.sin(2 * math.pi / n))
        attained = abs(abs(math.atan2(z.imag, z.real)) - (math.pi / 2 - math.pi / n)) < 1e-12
        good = worst <= 1e-9 and attained
        ok &= good
        print(f'n={n} max(sum cos - n cos(pi/n)) = {worst:.3e}  attained_by_scalar={attained}  {"OK" if good else "FAIL"}')
    print('ALL OK' if ok else 'FAILURES')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
