"""Negative association (beyond pairs) for the lambda-weighted uniform forest / connected spanning
subgraph measures on small 2-connected graphs.

NA: for disjoint edge sets S1, S2 and increasing events U1 (depending on S1), U2 (on S2),
P(U1 and U2) <= P(U1) P(U2).  Increasing functions are nonnegative combinations of up-set
indicators plus constants, so it suffices to test all pairs of up-sets of the Boolean lattices on
S1 and S2.  We test |S1| = |S2| = k (k = 3 by default; smaller sets are covered because an up-set
of 2^S may ignore coordinates).

usage: python3 na_scan.py MODEL K1 K2 n1 [n2 ...]   (MODEL = Z forests | C connected)
Uniform measure (lambda = 1), exact integer arithmetic: Cov * Z^2 = Z N(U1 U2) - N(U1) N(U2).
"""
import itertools, subprocess, sys
from fractions import Fraction
import numpy as np


def g6(line):
    n = ord(line[0]) - 63
    bits = []
    for ch in line[1:]:
        v = ord(ch) - 63
        bits += [(v >> (5 - i)) & 1 for i in range(6)]
    E, b = [], 0
    for j in range(1, n):
        for i in range(j):
            if bits[b]:
                E.append((i, j))
            b += 1
    return n, E


def objects(n, E, model):
    m = len(E)
    out = []
    for mask in range(1 << m):
        p = list(range(n))

        def find(x):
            while p[x] != x:
                p[x] = p[p[x]]
                x = p[x]
            return x
        ok = True
        if model == 'Z':
            for i in range(m):
                if mask >> i & 1:
                    a, b = find(E[i][0]), find(E[i][1])
                    if a == b:
                        ok = False
                        break
                    p[a] = b
        elif model == 'C':
            for i in range(m):
                if mask >> i & 1:
                    p[find(E[i][0])] = find(E[i][1])
            ok = len({find(x) for x in range(n)}) == 1
        else:  # control 'K': edge sets containing a cycle (an up-set; expected positive correlations)
            cyc = False
            for i in range(m):
                if mask >> i & 1:
                    a, b = find(E[i][0]), find(E[i][1])
                    if a == b:
                        cyc = True
                    p[a] = b
            ok = cyc
        if ok:
            out.append(mask)
    return np.array(out, dtype=np.int64)


def upsets(k):
    """all up-sets of the Boolean lattice 2^[k] as 0/1 vectors over 2^k points (excluding empty/full)."""
    pts = list(range(1 << k))
    res = []
    for bits in range(1 << (1 << k)):
        U = [(bits >> x) & 1 for x in pts]
        ok = all(not U[x] or U[y] for x in pts for y in pts if (x & y) == x)
        if ok and 0 < sum(U) < len(pts):
            res.append(U)
    return np.array(res, dtype=np.float64), res


def main():
    model, k1, k2 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    U1f, _ = upsets(k1)
    U2f, _ = upsets(k2)
    U1 = U1f.astype(np.int64); U2 = U2f.astype(np.int64)
    worst = -1.0
    worst_at = None
    checked = 0
    cand = []
    for nn in map(int, sys.argv[4:]):
        lines = subprocess.run(['./geng', '-Cq', str(nn)], capture_output=True, text=True).stdout.split()
        for line in lines:
            n, E = g6(line)
            m = len(E)
            if m < k1 + k2:
                continue
            obj = objects(n, E, model)
            Z = len(obj)
            bitcols = [((obj >> i) & 1) for i in range(m)]
            for S1 in itertools.combinations(range(m), k1):
                rest = [i for i in range(m) if i not in S1]
                pat1 = sum(bitcols[S1[t]] << t for t in range(k1))
                for S2 in itertools.combinations(rest, k2):
                    if k1 == k2 and S2 < S1:
                        continue  # unordered pair
                    pat2 = sum(bitcols[S2[t]] << t for t in range(k2))
                    J = np.zeros((1 << k1, 1 << k2), dtype=np.int64)
                    np.add.at(J, (pat1, pat2), 1)
                    A = U1 @ J            # rows: up-sets on S1, cols: points of S2
                    NAB = A @ U2.T        # N(U1 and U2)
                    NA = U1 @ J.sum(1)    # N(U1)
                    NB = U2 @ J.sum(0)    # N(U2)
                    C = Z * NAB - np.outer(NA, NB)
                    mx = int(C.max())
                    checked += C.size
                    if mx > worst:
                        worst = mx
                        worst_at = (line, S1, S2)
                    if mx > 0:
                        cand.append((line, S1, S2))
    print(f'model={model} k1={k1} k2={k2} uniform up-set pairs checked={checked} max Z^2*Cov={worst} at {worst_at} violations={len(cand)}')
    for c in cand[:5]:
        print('CANDIDATE', c)


if __name__ == '__main__':
    main()
