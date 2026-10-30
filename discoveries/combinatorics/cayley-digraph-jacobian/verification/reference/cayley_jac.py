"""Reiner's question (BIRS sandpile problems, 1.9): for a finite abelian group A and a multiset S of
nonzero elements with sum 0 (generating A), is Jac(Cay(A,S)) ~= A only when A is cyclic and
S = {a, -a} for a generator a?

Cay(A,S) is the Cayley digraph (arc g -> g + s for each s in S, with multiplicity).  It is
Eulerian, so its Jacobian is the cokernel of the reduced Laplacian (independent of the removed
vertex).  We compute invariant factors by an exact integer Smith normal form.

usage: python3 cayley_jac.py MAXORDER MAXSIZE
"""
import itertools, sys
from math import gcd
from collections import Counter


def smith_invariants(M):
    """invariant factors (>1) of an integer matrix (list of lists), exact."""
    A = [row[:] for row in M]
    m, n = len(A), len(A[0]) if A else 0
    inv = []
    r = 0
    for c in range(min(m, n)):
        # find nonzero pivot with minimal abs value in submatrix
        while True:
            piv = None
            for i in range(r, m):
                for j in range(r, n):
                    if A[i][j] and (piv is None or abs(A[i][j]) < abs(A[piv[0]][piv[1]])):
                        piv = (i, j)
            if piv is None:
                return [d for d in inv if d > 1], r
            i, j = piv
            A[r], A[i] = A[i], A[r]
            for row in A:
                row[r], row[j] = row[j], row[r]
            p = A[r][r]
            done = True
            for i in range(r + 1, m):
                q = A[i][r] // p
                if q:
                    A[i] = [a - q * b for a, b in zip(A[i], A[r])]
                if A[i][r]:
                    done = False
            for j in range(r + 1, n):
                q = A[r][j] // p
                if q:
                    for row in A:
                        row[j] -= q * row[r]
                if A[r][j]:
                    done = False
            if done:
                # divisibility: ensure p divides all remaining entries
                bad = None
                for i in range(r + 1, m):
                    for j in range(r + 1, n):
                        if A[i][j] % p:
                            bad = (i, j)
                            break
                    if bad:
                        break
                if bad:
                    i, j = bad
                    A[r] = [a + b for a, b in zip(A[r], A[i])]
                    continue
                inv.append(abs(p))
                r += 1
                break
    return [d for d in inv if d > 1], r


def group_elements(ds):
    return list(itertools.product(*[range(d) for d in ds]))


def add(x, y, ds):
    return tuple((a + b) % d for a, b, d in zip(x, y, ds))


def generates(S, ds):
    elems = {tuple([0] * len(ds))}
    frontier = list(elems)
    while frontier:
        x = frontier.pop()
        for s in S:
            y = add(x, s, ds)
            if y not in elems:
                elems.add(y)
                frontier.append(y)
    total = 1
    for d in ds:
        total *= d
    return len(elems) == total


def jac(ds, S):
    G = group_elements(ds)
    idx = {g: i for i, g in enumerate(G)}
    n = len(G)
    L = [[0] * n for _ in range(n)]
    for g in G:
        i = idx[g]
        for s in S:
            L[i][i] += 1
            L[i][idx[add(g, s, ds)]] -= 1
    red = [row[1:] for row in L[1:]]
    invs, rank = smith_invariants(red)
    assert rank == n - 1
    return invs


def invariant_factors_of_group(ds):
    # A = prod Z_d; compute invariant factors via Smith form of diag(ds)
    D = [[ds[i] if i == j else 0 for j in range(len(ds))] for i in range(len(ds))]
    invs, _ = smith_invariants(D)
    return sorted(invs)


def abelian_groups(order):
    """invariant-factor decompositions d1 | d2 | ... with product = order (d1 >= 2)."""
    out = []

    def rec(rem, prev, acc):
        if rem == 1:
            out.append(tuple(acc))
            return
        for d in range(2, rem + 1):
            if rem % d == 0 and (prev is None or d % prev == 0):
                # remaining must be divisible-chain compatible: rem/d must be a product of multiples of d
                rec(rem // d, d, acc + [d])
    rec(order, None, [])
    return [g for g in out if all(g[i + 1] % g[i] == 0 for i in range(len(g) - 1))]


def main():
    maxorder, maxsize = int(sys.argv[1]), int(sys.argv[2])
    tested = 0
    hits = []
    for order in range(2, maxorder + 1):
        for ds in abelian_groups(order):
            target = invariant_factors_of_group(ds)
            nz = [g for g in group_elements(ds) if any(g)]
            for size in range(2, maxsize + 1):
                for S in itertools.combinations_with_replacement(nz, size):
                    tot = tuple(sum(c) % d for c, d in zip(zip(*S), ds))
                    if any(tot):
                        continue
                    if not generates(S, ds):
                        continue
                    tested += 1
                    J = sorted(jac(ds, S))
                    if J == target:
                        cyclic_pm = (len(ds) == 1 and size == 2)
                        hits.append((ds, S, cyclic_pm))
                        if not cyclic_pm:
                            print('COUNTEREXAMPLE', ds, S, J, flush=True)
    nontriv = [h for h in hits if not h[2]]
    print(f'max order {maxorder}, |S| <= {maxsize}: tested {tested} (A,S); Jac ~= A in {len(hits)} cases, '
          f'of which not of the form (cyclic, {{a,-a}}): {len(nontriv)}')


if __name__ == '__main__':
    main()
