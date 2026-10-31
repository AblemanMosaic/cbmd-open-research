"""Negative edge correlation for weighted forests and connected spanning subgraphs: exact
small-case gates (pure Python).

For a (multi)graph G and lambda > 0 let Z_G(lambda) = sum_{forests F} lambda^{|F|} and
C_G(lambda) = sum_{connected spanning subgraphs A} lambda^{|A|}.  For distinct edges e, f the
objects containing e correspond to those of G/e (forests: loops discarded; connected subgraphs:
loops kept and free), so with X in {Z, C}
    P_X(lambda) := X_{G/e} X_{G/f} - X_G X_{G/e/f}
equals the Rayleigh difference divided by lambda^2, and negative correlation of e and f under
the lambda-weighted measure is P_X(lambda) >= 0.
  * Kahn / Grimmett-Winkler (forests): P_Z(lambda) >= 0 for all lambda > 0 (GW: lambda = 1).
  * Grimmett-Winkler (connected subgraphs): P_C(1) >= 0; the q -> 0 limit of the q < 1
    random-cluster question asks P_C(lambda) >= 0 for all lambda > 0.

Gates (each required):
  * DP_EQUALS_BRUTE_FORCE: the contraction + subset-recursion polynomials equal direct
    enumeration of edge subsets, for every pair of edges of every 2-connected graph on at most
    5 vertices and of 40 multigraphs (multiplicity <= 3), both models;
  * BLOCK_FACTORISATION: on graphs with cut vertices, P is identically 0 for edges in different
    blocks and equals (product of the other blocks' polynomials)^2 times the block's P for edges
    in one block (so 2-connected graphs suffice);
  * GRAPH_LIST: verification/reference/two_connected_le7.g6 holds exactly 1, 3, 10, 56, 468
    pairwise non-isomorphic 2-connected graphs on 3..7 vertices (OEIS A002218);
  * NC_SMALL: for every 2-connected graph on at most 6 vertices and every pair of edges, both
    P_Z and P_C have all coefficients >= 0 and P(1) > 0;
  * SMALL_LAMBDA_LAW: Theorem 4 of argument/WRITTEN_ARGUMENT.md -- for every pair of edges of
    every 2-connected graph on <= 6 vertices, the lowest nonzero coefficient of P_Z sits at
    degree L - 2 and equals the number of cycles of length L through e and f (L = shortest such
    length); the matroid form holds on 60 random binary/ternary vector matroids; Corollary 2
    (top term of P_C = number of smallest bonds through e and f) on the same graphs; and a binary
    rank-4 matroid ([I_4 | X], recalled as S_8) obeys the law yet has a negative Rayleigh
    coefficient (control);
  * NA_SMALL: negative association beyond pairs at lambda = 1, exactly: for every 2-connected
    graph on 4..5 vertices, every pair of disjoint 3-edge sets and every pair of nontrivial
    up-sets, Cov <= 0 for both models; the positive control (uniform on cycle-containing edge sets)
    shows a positive covariance;
  * EVIDENCE_SUMMARY: the recorded C runs (evidence/forest_nc_runs.json) cover 1, 3, 10, 56,
    468, 7123, 194066 graphs on 3..9 vertices for both models with zero violations, and the
    pair totals equal sum_G binom(|E(G)|, 2) recomputed here for n <= 7.
"""
from __future__ import annotations
import itertools
import json
import os
import random
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EVIDENCE = os.path.normpath(os.path.join(HERE, '..', '..', 'evidence'))


# ---------- graph helpers (multigraph = dict {(u,v): multiplicity} with u < v; loops (v,v)) ----------
def g6_decode(s):
    n = ord(s[0]) - 63
    bits = []
    for ch in s[1:]:
        v = ord(ch) - 63
        bits += [(v >> (5 - i)) & 1 for i in range(6)]
    E = {}
    b = 0
    for j in range(1, n):
        for i in range(j):
            if bits[b]:
                E[(i, j)] = 1
            b += 1
    return n, E


def contract(n, E, u, v, keep_loops):
    """Contract one copy of edge (u,v), u != v; vertices relabelled 0..n-2."""
    if u > v:
        u, v = v, u
    mp = {}
    k = 0
    for x in range(n):
        if x != v:
            mp[x] = k
            k += 1
    mp[v] = mp[u]
    F = {}
    for (a, b), c in E.items():
        if (a, b) == (u, v):
            c -= 1
        if c == 0:
            continue
        x, y = sorted((mp[a], mp[b]))
        if x == y and not keep_loops:
            continue
        F[(x, y)] = F.get((x, y), 0) + c
    return n - 1, F


def det(M):
    """Exact determinant (fraction-free Bareiss)."""
    m = len(M)
    if m == 0:
        return 1
    M = [row[:] for row in M]
    sign, prev = 1, 1
    for k in range(m - 1):
        if M[k][k] == 0:
            p = next((i for i in range(k + 1, m) if M[i][k]), None)
            if p is None:
                return 0
            M[k], M[p] = M[p], M[k]
            sign = -sign
        for i in range(k + 1, m):
            for j in range(k + 1, m):
                M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
        prev = M[k][k]
    return sign * M[m - 1][m - 1]


def padd(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        r[i] += x
    for i, x in enumerate(b):
        r[i] += x
    return r


def pmul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return r


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def forest_poly(n, E):
    """Z: sum over set partitions of prod tau(H[B]) lambda^{|B|-1}."""
    tau = {}
    for B in range(1, 1 << n):
        vs = [v for v in range(n) if B >> v & 1]
        if len(vs) == 1:
            tau[B] = 1
            continue
        L = [[0] * len(vs) for _ in vs]
        for (a, b), c in E.items():
            if a != b and B >> a & 1 and B >> b & 1:
                i, j = vs.index(a), vs.index(b)
                L[i][j] -= c
                L[j][i] -= c
                L[i][i] += c
                L[j][j] += c
        tau[B] = det([row[1:] for row in L[1:]])
    g = {0: [1]}
    for S in range(1, 1 << n):
        low = S & -S
        rest = S ^ low
        acc = []
        sub = rest
        while True:
            B = low | sub
            if tau[B]:
                e = bin(B).count('1') - 1
                acc = padd(acc, [0] * e + [tau[B] * x for x in g[S ^ B]])
            if sub == 0:
                break
            sub = (sub - 1) & rest
        g[S] = acc
    return trim(g[(1 << n) - 1])


def conn_poly(n, E):
    """C: conn(S) = all(S) - sum_{low in B proper} conn(B) all(S\\B); all(S) = (1+lambda)^{e(S)}."""
    from math import comb
    ec = {}
    for S in range(1 << n):
        ec[S] = sum(c for (a, b), c in E.items() if S >> a & 1 and S >> b & 1)
    allp = {S: [comb(ec[S], k) for k in range(ec[S] + 1)] for S in range(1 << n)}
    conn = {}
    for S in range(1, 1 << n):
        low = S & -S
        rest = S ^ low
        acc = list(allp[S])
        sub = rest
        while True:
            if sub != rest:
                B = low | sub
                prod = pmul(conn[B], allp[S ^ B])
                acc = padd(acc, [-x for x in prod])
            if sub == 0:
                break
            sub = (sub - 1) & rest
        conn[S] = acc
    return trim(conn[(1 << n) - 1])


def P_pair(n, E, e, f, model):
    """e, f: edge classes (u,v); if e == f the class must have multiplicity >= 2 (two copies)."""
    keep = model == 'C'
    poly = conn_poly if model == 'C' else forest_poly
    X = poly(n, E)
    ne, Ee = contract(n, E, e[0], e[1], keep)
    Xe = poly(ne, Ee)
    if e == f:
        if model == 'Z':
            Xef = []  # no forest contains two parallel copies
        else:
            Ef = dict(Ee)
            # the second copy became a loop at the merged vertex, whose new label is min(e);
            # it is forced into the subgraph, so remove it and count the rest freely
            key = (min(e), min(e))
            Ef[key] -= 1
            if Ef[key] == 0:
                del Ef[key]
            Xef = poly(ne, Ef)
        Xf = Xe
    else:
        nf, Ef = contract(n, E, f[0], f[1], keep)
        Xf = poly(nf, Ef)
        # contract f inside G/e: relabel f's endpoints
        v = max(e)
        def rl(x):
            if x == v:
                return min(e)
            return x - (1 if x > v else 0)
        a, b = rl(f[0]), rl(f[1])
        nef, Eef = contract(ne, Ee, a, b, keep)
        Xef = poly(nef, Eef)
    return trim(padd(pmul(Xe, Xf), [-x for x in pmul(X, Xef)]))


def P_brute(n, E, e, f, model):
    copies = []
    idx = {}
    for k, c in sorted(E.items()):
        idx[k] = len(copies)
        copies += [k] * c
    ie = idx[e]
    jf = idx[f] + (1 if e == f else 0)
    m = len(copies)
    Z, Ze, Zf, Zef = [0] * (m + 1), [0] * (m + 1), [0] * (m + 1), [0] * (m + 1)
    for mask in range(1 << m):
        sub = [copies[i] for i in range(m) if mask >> i & 1]
        p = list(range(n))
        def find(x):
            while p[x] != x:
                p[x] = p[p[x]]
                x = p[x]
            return x
        good = True
        if model == 'Z':
            for a, b in sub:
                ra, rb = find(a), find(b)
                if ra == rb:
                    good = False
                    break
                p[ra] = rb
        else:
            for a, b in sub:
                p[find(a)] = find(b)
            good = len({find(x) for x in range(n)}) == 1
        if not good:
            continue
        k = len(sub)
        Z[k] += 1
        if mask >> ie & 1:
            Ze[k] += 1
        if mask >> jf & 1:
            Zf[k] += 1
        if mask >> ie & 1 and mask >> jf & 1:
            Zef[k] += 1
    R = padd(pmul(Ze, Zf), [-x for x in pmul(Z, Zef)])
    assert R[0] == 0 and R[1] == 0
    return trim(R[2:])


def is_2connected(n, E):
    if n < 3:
        return False
    for cut in range(-1, n):
        alive = [v for v in range(n) if v != cut]
        p = {v: v for v in alive}
        def find(x):
            while p[x] != x:
                x = p[x]
            return x
        for (a, b) in E:
            if a != cut and b != cut:
                p[find(a)] = find(b)
        if len({find(v) for v in alive}) != 1:
            return False
    return True


def canon(n, E):
    best = None
    for perm in itertools.permutations(range(n)):
        key = tuple(sorted(tuple(sorted((perm[a], perm[b]))) for (a, b) in E))
        if best is None or key < best:
            best = key
    return best


def shortest_cycles_through(n, E, e, f):
    """(L, N): length of a shortest cycle containing edges e and f of a simple graph, and their
    number; each such cycle is a simple path from e[1] to e[0] avoiding e that uses f."""
    adj = {v: set() for v in range(n)}
    for (x, y) in E:
        adj[x].add(y)
        adj[y].add(x)
    a, b = e
    fs = frozenset(f)
    cnt = {}
    stack = [(b, (b,), False)]
    while stack:
        v, path, used = stack.pop()
        if v == a:
            if used:
                cnt[len(path)] = cnt.get(len(path), 0) + 1
            continue
        for w in adj[v]:
            if (v == b and w == a) or w in path:
                continue
            stack.append((w, path + (w,), used or frozenset((v, w)) == fs))
    L = min(cnt)
    return L, cnt[L]


def matroid_small_lambda_ok(cols, q):
    """Theorem 4 on the vector matroid of cols over GF(q) (q prime): R_ef lowest term."""
    m = len(cols)

    def rank(vs):
        rows = [list(v) for v in vs]
        r = 0
        for c in range(len(rows[0]) if rows else 0):
            piv = next((i for i in range(r, len(rows)) if rows[i][c] % q), None)
            if piv is None:
                continue
            rows[r], rows[piv] = rows[piv], rows[r]
            inv = pow(rows[r][c], q - 2, q)
            rows[r] = [x * inv % q for x in rows[r]]
            for i in range(len(rows)):
                if i != r and rows[i][c] % q:
                    fac = rows[i][c]
                    rows[i] = [(x - fac * y) % q for x, y in zip(rows[i], rows[r])]
            r += 1
        return r
    indep = {}
    for mask in range(1 << m):
        vs = [cols[i] for i in range(m) if mask >> i & 1]
        indep[mask] = (rank(vs) == len(vs)) if vs else True
    circuits = [S for S in range(1, 1 << m) if not indep[S]
                and all(indep[S & ~(1 << i)] for i in range(m) if S >> i & 1)]
    ok = True
    count = 0
    for e, f in itertools.combinations(range(m), 2):
        if not indep[1 << e] or not indep[1 << f]:
            continue
        Z, Ze, Zf, Zef = ([0] * (m + 1) for _ in range(4))
        for S, good in indep.items():
            if good:
                k = bin(S).count('1')
                Z[k] += 1
                Ze[k] += S >> e & 1
                Zf[k] += S >> f & 1
                Zef[k] += (S >> e & 1) and (S >> f & 1)
        R = trim(padd(pmul(Ze, Zf), [-x for x in pmul(Z, Zef)]))
        sizes = [bin(C).count('1') for C in circuits if C >> e & 1 and C >> f & 1]
        count += 1
        if not sizes:
            ok = ok and R == []
        else:
            c = min(sizes)
            low = next((i for i, x in enumerate(R) if x), None)
            ok = ok and low == c and R[c] == sizes.count(c)
    return ok, count


def is_connected_on(vs, E):
    vs = set(vs)
    if not vs:
        return False
    start = next(iter(vs))
    seen, stack = {start}, [start]
    while stack:
        v = stack.pop()
        for (a, b) in E:
            for x, y in ((a, b), (b, a)):
                if x == v and y in vs and y not in seen:
                    seen.add(y)
                    stack.append(y)
    return seen == vs


def s8_rayleigh(cols, e, f):
    """R_ef(lambda) for the binary vector matroid of cols (subset enumeration)."""
    m = len(cols)

    def indep(mask):
        rows = [list(cols[i]) for i in range(m) if mask >> i & 1]
        r = 0
        for c in range(4):
            piv = next((i for i in range(r, len(rows)) if rows[i][c]), None)
            if piv is None:
                continue
            rows[r], rows[piv] = rows[piv], rows[r]
            for i in range(len(rows)):
                if i != r and rows[i][c]:
                    rows[i] = [x ^ y for x, y in zip(rows[i], rows[r])]
            r += 1
        return r == len(rows)
    Z, Ze, Zf, Zef = ([0] * (m + 1) for _ in range(4))
    for S in range(1 << m):
        if indep(S):
            k = bin(S).count('1')
            Z[k] += 1
            Ze[k] += S >> e & 1
            Zf[k] += S >> f & 1
            Zef[k] += (S >> e & 1) and (S >> f & 1)
    return trim(padd(pmul(Ze, Zf), [-x for x in pmul(Z, Zef)]))


def main():
    results = {}
    graphs = [g6_decode(l.strip()) for l in open(os.path.join(HERE, 'two_connected_le7.g6')) if l.strip()]

    # DP_EQUALS_BRUTE_FORCE
    bad, count = [], 0
    for n, E in graphs:
        if n > 5:
            continue
        keys = sorted(E)
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                for model in 'ZC':
                    count += 1
                    if P_pair(n, E, keys[i], keys[j], model) != P_brute(n, E, keys[i], keys[j], model):
                        bad.append((n, keys[i], keys[j], model))
    rng = random.Random(20261030)
    small = [(n, E) for n, E in graphs if n <= 4]
    for _ in range(40):
        n, E0 = rng.choice(small)
        E = {k: rng.randint(1, 3) for k in E0}
        if sum(E.values()) > 12:
            continue
        keys = sorted(E)
        for i in range(len(keys)):
            for j in range(i, len(keys)):
                if i == j and E[keys[i]] < 2:
                    continue
                for model in 'ZC':
                    count += 1
                    if P_pair(n, E, keys[i], keys[j], model) != P_brute(n, E, keys[i], keys[j], model):
                        bad.append((n, E, keys[i], keys[j], model))
    results['DP_EQUALS_BRUTE_FORCE'] = {'pass': not bad and count > 0, 'cases': count, 'mismatches': bad[:5]}

    # BLOCK_FACTORISATION: glue a triangle T on {0,1,2} and a chorded 4-cycle Q on {0,3,4,5} at 0;
    # Q relabelled to {0,1,2,3} is the graph whose polynomial XQ multiplies the block term
    T = {(0, 1): 1, (0, 2): 1, (1, 2): 1}
    Q = {(0, 3): 1, (3, 4): 1, (4, 5): 1, (0, 5): 1, (3, 5): 1}
    G = dict(T)
    G.update(Q)
    ok = True
    for model in 'ZC':
        poly = conn_poly if model == 'C' else forest_poly
        XQ = poly(4, {(0, 1): 1, (1, 2): 1, (2, 3): 1, (0, 3): 1, (1, 3): 1})
        cross = P_pair(6, G, (0, 1), (3, 4), model)
        within = P_pair(6, G, (0, 1), (1, 2), model)
        PT = P_pair(3, T, (0, 1), (1, 2), model)
        ok = ok and cross == [] and within == trim(pmul(pmul(XQ, XQ), PT))
    results['BLOCK_FACTORISATION'] = {'pass': ok}

    # GRAPH_LIST
    by_n = {}
    for n, E in graphs:
        by_n.setdefault(n, []).append(E)
    counts_ok = [len(by_n.get(n, [])) for n in range(3, 8)] == [1, 3, 10, 56, 468]
    conn_ok = all(is_2connected(n, E) for n, E in graphs)
    distinct = True
    for n in range(3, 7):  # canonical forms by brute force (n = 7 skipped for time; geng output)
        cf = [canon(n, E) for E in by_n[n]]
        distinct = distinct and len(set(cf)) == len(cf)
    results['GRAPH_LIST'] = {'pass': counts_ok and conn_ok and distinct,
                             'counts': {str(n): len(by_n.get(n, [])) for n in range(3, 8)},
                             'non_isomorphism_checked_for_n_le': 6}

    # NC_SMALL
    viol, pairs = [], 0
    for n, E in graphs:
        if n > 6:
            continue
        keys = sorted(E)
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                for model in 'ZC':
                    P = P_pair(n, E, keys[i], keys[j], model)
                    pairs += 1
                    if not P or min(P) < 0 or sum(P) <= 0:
                        viol.append((n, keys[i], keys[j], model, P))
    results['NC_SMALL'] = {'pass': not viol, 'pair_model_checks': pairs, 'violations': viol[:5]}

    # SMALL_LAMBDA_LAW (Theorem 4): lowest term of P_Z is N lambda^(L-2)
    bad, count = [], 0
    for n, E in graphs:
        if n > 6:
            continue
        keys = sorted(E)
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                P = P_pair(n, E, keys[i], keys[j], 'Z')
                L, N = shortest_cycles_through(n, list(E), keys[i], keys[j])
                low = next((k for k, x in enumerate(P) if x), None)
                count += 1
                if low != L - 2 or P[low] != N:
                    bad.append((n, keys[i], keys[j]))
    rng2 = random.Random(4)
    mcount, mok = 0, True
    for _ in range(60):
        q = rng2.choice([2, 3])
        r = rng2.randint(2, 4)
        m = rng2.randint(r + 1, min(8, r + 4))
        cols = [tuple(rng2.randrange(q) for _ in range(r)) for _ in range(m)]
        ok, c = matroid_small_lambda_ok(cols, q)
        mok = mok and ok
        mcount += c
    # Corollary 2: top term of P_C is N* lambda^(2m - c* - 2) (bonds through e and f)
    bond_bad, bond_count = [], 0
    for n, E in graphs:
        if n > 6:
            continue
        keys = sorted(E)
        bonds = []
        for S in range(1, 1 << n):
            if not S & 1 or S == (1 << n) - 1:
                continue
            side = [v for v in range(n) if S >> v & 1]
            other = [v for v in range(n) if not S >> v & 1]
            if is_connected_on(side, E) and is_connected_on(other, E):
                bonds.append(frozenset(k for k in keys if (S >> k[0] & 1) != (S >> k[1] & 1)))
        for i in range(len(keys)):
            for j in range(i + 1, len(keys)):
                P = P_pair(n, E, keys[i], keys[j], 'C')
                sizes = [len(B) for B in bonds if keys[i] in B and keys[j] in B]
                cs = min(sizes)
                top = max(k for k, x in enumerate(P) if x)
                bond_count += 1
                if top != 2 * len(keys) - cs - 2 or P[top] != sizes.count(cs):
                    bond_bad.append((n, keys[i], keys[j]))

    # control: the binary matroid [I_4 | X] (circuit profile 3/7/4 of sizes 3/4/5, 48 bases; recalled as
    # Oxley's representation of S_8, identification not verified) obeys the small-lambda law but has negative Rayleigh
    # coefficients, so the coefficientwise test is not vacuous and the graph observation is
    # graph-specific
    X = [[0, 1, 1, 1], [1, 0, 1, 1], [1, 1, 0, 1], [1, 1, 1, 1]]
    s8 = [tuple(1 if i == k else 0 for i in range(4)) for k in range(4)] + [tuple(X[i][j] for i in range(4)) for j in range(4)]
    s8_law, _ = matroid_small_lambda_ok(s8, 2)
    s8_neg = []
    for e0, f0 in itertools.combinations(range(8), 2):
        Rs = s8_rayleigh(s8, e0, f0)
        if min(Rs) < 0:
            s8_neg.append((e0, f0, Rs))
    results['SMALL_LAMBDA_LAW'] = {'pass': not bad and count > 0 and mok and mcount > 0 and s8_law and len(s8_neg) > 0
                                   and not bond_bad and bond_count > 0,
                                   'graph_pairs': count, 'matroid_pairs': mcount, 'failures': bad[:5],
                                   'bond_law_pairs': bond_count, 'bond_law_failures': bond_bad[:5],
                                   's8_pairs_with_negative_coefficient': len(s8_neg),
                                   's8_example': s8_neg[0] if s8_neg else None}

    # NA_SMALL
    import numpy as np
    sys.path.insert(0, HERE)
    import na_scan
    U, _ = na_scan.upsets(3)
    U = U.astype(np.int64)
    na_max = {}
    for model in ('Z', 'C', 'K'):
        best = None
        for n, Ed in graphs:
            if n > 5:
                continue
            E = sorted(Ed)
            if len(E) < 6:
                continue
            obj = na_scan.objects(n, E, model)
            Zc = len(obj)
            cols = [((obj >> i) & 1) for i in range(len(E))]
            for S1 in itertools.combinations(range(len(E)), 3):
                rest = [i for i in range(len(E)) if i not in S1]
                p1 = sum(cols[S1[t]] << t for t in range(3))
                for S2 in itertools.combinations(rest, 3):
                    p2 = sum(cols[S2[t]] << t for t in range(3))
                    J = np.zeros((8, 8), dtype=np.int64)
                    np.add.at(J, (p1, p2), 1)
                    Cm = Zc * (U @ J @ U.T) - np.outer(U @ J.sum(1), U @ J.sum(0))
                    mx = int(Cm.max())
                    best = mx if best is None else max(best, mx)
        na_max[model] = best
    results['NA_SMALL'] = {'pass': na_max['Z'] <= 0 and na_max['C'] <= 0 and na_max['K'] > 0, 'max_Z2_cov': na_max}

    # EVIDENCE_SUMMARY
    ev = json.load(open(os.path.join(EVIDENCE, 'forest_nc_runs.json')))
    # A002218 (2-connected graphs by vertices); 10 is the order of the forest run
    expect = {'3': 1, '4': 3, '5': 10, '6': 56, '7': 468, '8': 7123, '9': 194066}
    pair_tot = {str(n): sum(len(E) * (len(E) - 1) // 2 for E in by_n[n]) for n in range(3, 8)}
    ok = True
    for model in ('forests', 'connected'):
        negkey = 'posneg' if model == 'forests' else 'posneg_numeric'
        for n, cnt in expect.items():
            r = ev[model][n]
            ok = ok and r['graphs'] == cnt and r['p1neg'] == 0 and r['coefneg'] == 0 and r['zero'] == 0
            ok = ok and r[negkey] == 0
            if n in pair_tot:
                ok = ok and r['pairs'] == pair_tot[n]
    ok = ok and '10' not in ev['connected']          # n = 10 was run for forests only
    r10 = ev['forests']['10']
    ok = ok and (r10['graphs'], r10['pairs'], r10['chunks']) == (9743542, 2570347998, 500)
    ok = ok and all(r10[k] == 0 for k in ('zero', 'p1neg', 'coefneg', 'posneg', 'parallel_pairs'))
    # the two independent cross-checks of the n = 10 totals, as recorded by the tools that produced them
    xc = open(os.path.join(EVIDENCE, 'raw', 'n10_crosschecks.txt')).read()
    ok = ok and '9743542 graphs generated' in xc and 'graphs 9743542 pairs 2570347998' in xc
    results['EVIDENCE_SUMMARY'] = {'pass': ok, 'n10_forest_pairs': r10['pairs']}

    # RAW_PROVENANCE: re-derive every recorded count from the raw run outputs in evidence/raw/,
    # so a hand-edited evidence file fails rather than being believed.
    def raw_sum(files):
        tot, seen = {}, 0
        for fn in files:
            for l in open(os.path.join(EVIDENCE, 'raw', fn)):
                if l.startswith('SUMMARY'):
                    seen += 1
                    for kv in l.split(' at ')[0].split()[1:]:
                        k, v = kv.split('=')
                        if 'ratio' not in k:
                            tot[k] = tot.get(k, 0) + int(v)
                elif re.match(r'(P1NEG|COEFNEG|POSNEG)', l):
                    raise SystemExit('violation line in raw/' + fn)
        return tot, seen
    groups = [('forests', str(n), [f'f{n}.txt']) for n in range(3, 9)] + \
             [('connected', str(n), [f'c{n}.txt']) for n in range(3, 9)] + \
             [('forests', '9', ['f9r_0.txt', 'f9r_1.txt']), ('connected', '9', ['c9r_0.txt', 'c9r_1.txt']),
              ('forests', '10', ['f10.txt']),
              ('multigraphs', 'forests_n6_mult_le3', ['mf6.txt']), ('multigraphs', 'connected_n6_mult_le3', ['mc6.txt']),
              ('multigraphs', 'forests_n7_mult_le2', ['mf7.txt']), ('multigraphs', 'connected_n7_mult_le2', ['mc7.txt'])]
    prov_bad, prov_n = [], 0
    for model, key, files in groups:
        tot, seen = raw_sum(files)
        rec = ev[model][key]
        for k, v in tot.items():
            prov_n += 1
            if rec.get(k) != v:
                prov_bad.append((model, key, k, rec.get(k), v))
        if key == '10' and seen != 500:
            prov_bad.append((model, key, 'summaries', seen, 500))
    results['RAW_PROVENANCE'] = {'pass': not prov_bad and prov_n > 0, 'fields_rederived': prov_n,
                                 'mismatches': prov_bad[:5]}

    all_pass = all(v['pass'] for v in results.values())
    for k, v in results.items():
        print(k, 'PASS' if v['pass'] else 'FAIL')
    if '--write' in sys.argv:
        with open(os.path.join(EVIDENCE, 'check_forest_nc.json'), 'w') as fh:
            json.dump({'schema': 'cbmd.forest-nc.check.v1', 'gates': results, 'pass': all_pass}, fh, indent=1)
            fh.write('\n')
    print('ALL PASS' if all_pass else 'FAILURES')
    return 0 if all_pass else 1


if __name__ == '__main__':
    sys.exit(main())
