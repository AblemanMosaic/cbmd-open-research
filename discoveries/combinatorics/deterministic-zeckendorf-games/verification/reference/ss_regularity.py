"""Split Smallest is Fibonacci-regular: a computer-assisted proof from the exact formula.

The exact formula of the written argument (§4) gives S_SS(n) = T(w*) + E(w*, a),
and (w*, a) is the lazy Fibonacci representation y = lazy(n) of n (over
F_1 = 1, F_2 = 2, ...; no two consecutive 0's), split into all but its last
digit and its last digit. This script:

  1. builds weighted automata (exact rational linear representations) for
     * W(w)  = tr1(w) if w is in the counter language, else 0;
     * T(u)  = sum of tr1(w) over counter-language words w < u in radix order;
     * T'(y) = T(y minus its last letter);
     * E'(y) = the end-phase block sum, read from the right with carry 0;
     * S_lazy(y) = T'(y) + E'(y), ignoring leading zeros;
  2. builds the finite automaton Rel of aligned pairs (x, y): x a Zeckendorf
     word, y a lazy word padded with leading zeros, val(x) = val(y) (exact
     value-difference states (a, b), bounded by 12, trimmed);
  3. composes them into a representation SX of n -> S_lazy(lazy(n)) read on
     Zeckendorf words;
  4. decides SX = the 9-dimensional representation ss_linrep.json exactly, by
     the reachable-subspace (Schützenberger) equivalence test.

Gates (each required):
  * COMPONENT_W, COMPONENT_T: exhaustive on words of length <= 10;
  * COMPONENT_E: E' equals the end-phase formula on lazy(n), n < 800;
  * LAZY_IS_STOP: (w*, a) of the counter equals lazy(n) for n < 2000;
  * REL_SOUND: every Rel state satisfies its value invariant (by construction:
    e = a F_{j+1} + b F_j, accepted iff a + b = 0 at j = 0) -- checked on all
    aligned pairs of length <= 10;
  * REL_COMPLETE: Rel's domain contains every Zeckendorf word (subset
    construction against the Zeckendorf automaton), so with soundness and the
    uniqueness of lazy representations it accepts exactly (Zeck(n), lazy(n));
  * REL_BOUND_STABLE: bound 40 gives the same trimmed automaton;
  * SX_MATCHES_GAME: SX equals the simulated SS split count for n <= 600;
  * EQUIVALENT_TO_9DIM: SX minus the 9-dimensional representation (as a
    letter-level automaton) is identically zero;
  * BLOCK_LAW: S(F_k + m) - S(F_k) - S(m) depends only on m and k mod 2
    (for m < F_{k-1}), decided by finite linear algebra on the representation;
  * CLOSED_FORM_F_k and CLOSED_FORM_F_k_minus_1: S(F_k) = S(F_k - 1) =
    F_{k+1} - (2(k-1)^2 + 8(k-1) + 15 + (-1)^(k-1))/8 for k = 2..40, which is
    a proof because both sides are linear recurrence sequences in k of order
    <= 15 (9 from the representation, 6 from the closed form);
  * CONTROL: perturbing one entry of the 9-dimensional representation makes
    the equivalence test fail.
"""
from __future__ import annotations
import json
import sys
from fractions import Fraction as Fr
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from zeckendorf_games import end_phase_splits, play  # noqa: E402

F = [0, 1, 2]
while len(F) < 200:
    F.append(F[-1] + F[-2])


def in_L(w):
    i = w.find("00")
    if i < 0:
        return True
    return set(w[i + 2:]) <= {"1"} and "00" not in w[i + 1:]


def L_words(maxlen):
    out = [""]
    for l in range(1, maxlen + 1):
        for x in range(2 ** (l - 1), 2 ** l):
            w = bin(x)[2:]
            if in_L(w):
                out.append(w)
    return out


def zeck(n):
    if n == 0:
        return ""
    k = max(i for i in range(1, len(F)) if F[i] <= n)
    s = ""
    for i in range(k, 0, -1):
        if F[i] <= n:
            s += "1"
            n -= F[i]
        else:
            s += "0"
    return s

# ---------- generic representations: (lam, {letter: M}, gam), row-vector convention
def ev(rep, w):
    lam, M, gam = rep
    v = lam[:]
    for ch in w:
        A = M[ch]; n = len(v)
        v = [sum(v[i]*A[i][j] for i in range(n) if v[i]) for j in range(len(A[0]))]
    return sum(v[i]*gam[i] for i in range(len(v)))

def zeros(r, c): return [[Fr(0)]*c for _ in range(r)]

# ---------- W: weight tr1(w) on words of the language L (no leading zeros)
Q = ['S0', 'A1', 'A0', 'B']
delta = {('S0','1'):'A1', ('A1','1'):'A1', ('A1','0'):'A0', ('A0','1'):'A1', ('A0','0'):'B', ('B','1'):'B'}
acc = set(Q)
idx = {}
for q in Q:
    for k in ('one','t'): idx[(q,k)] = len(idx)
dW = len(idx)
MW = {}
for ch in '01':
    A = zeros(dW, dW)
    for q in Q:
        q2 = delta.get((q,ch))
        if q2 is None: continue
        A[idx[(q,'one')]][idx[(q2,'one')]] += 1
        if ch == '1':
            A[idx[(q,'t')]][idx[(q2,'t')]] += 1
            A[idx[(q,'one')]][idx[(q2,'t')]] += 1
    MW[ch] = A
lamW = [Fr(0)]*dW; lamW[idx[('S0','one')]] = Fr(1)
gamW = [Fr(0)]*dW
for q in acc: gamW[idx[(q,'t')]] = Fr(1)
W = (lamW, MW, gamW)

# ---------- T(u) = sum_{w in L, w < u (radix order)} tr1(w)
# components: wait0, wait1, follow[dW], free[dW]
dT = 2 + 2*dW
o_f, o_r = 2, 2 + dW
MT = {}
for ch in '01':
    A = zeros(dT, dT)
    A[0][1] += 1; A[1][1] += 1
    free_step = [[MW['0'][i][j] + MW['1'][i][j] for j in range(dW)] for i in range(dW)]
    # wait1 -> free: start W and read this letter freely
    for j in range(dW):
        A[1][o_r + j] += sum(lamW[i]*free_step[i][j] for i in range(dW))
    for i in range(dW):
        for j in range(dW):
            A[o_f+i][o_f+j] += MW[ch][i][j]        # follow
            A[o_r+i][o_r+j] += free_step[i][j]     # free
            if ch == '1':
                A[o_f+i][o_r+j] += MW['0'][i][j]   # branch below u
    MT[ch] = A
lamT = [Fr(0)]*dT; lamT[0] = Fr(1)
for i in range(dW): lamT[o_f+i] = lamW[i]
gamT = [Fr(0)]*dT
for i in range(dW): gamT[o_r+i] = gamW[i]
T = (lamT, MT, gamT)

# ---------- T'(y) = T(y without its last letter): extra component *
def drop_last(rep):
    lam, M, gam = rep; d = len(lam)
    M2 = {}
    for ch, A in M.items():
        B = zeros(d+1, d+1)
        for i in range(d):
            for j in range(d): B[i][j] = A[i][j]
            B[i][d] = gam[i]
        M2[ch] = B
    return (lam + [Fr(0)], M2, [Fr(0)]*d + [Fr(1)])
Tp = drop_last(T)

# ---------- E'(y): runs of 1s from the right, carry from 0 (reversed reading, then transposed)
G0, G1, R1, B1, Bm, Bm2, Be, ACC = range(8)
M1 = zeros(8, 8); M0 = zeros(8, 8)
M1[G0][R1] = 1
for s in (G1, R1):
    M1[s][B1] += 1; M1[s][Bm] += 2; M1[s][Bm2] += 4; M1[s][Be] += 1
M1[B1][B1] = 1; M1[B1][Bm] = 1; M1[B1][Bm2] = 1; M1[B1][Be] = 1
M1[Bm][Bm] = 1; M1[Bm][Bm2] = 2; M1[Bm2][Bm2] = 1; M1[Be][Be] = -1; M1[ACC][ACC] = 1
M0[G0][G0] = 1; M0[G1][G1] = 1; M0[R1][G0] = 1
M0[B1][G1] = 1; M0[B1][ACC] = Fr(1,4); M0[Bm][ACC] = Fr(-2,4); M0[Bm2][ACC] = Fr(1,4); M0[Be][ACC] = Fr(-1,4)
M0[ACC][ACC] = 1
lamE = [Fr(0)]*8; lamE[G0] = Fr(1)
gamE = [Fr(0)]*8; gamE[ACC] = Fr(1); gamE[B1] = Fr(1,4); gamE[Bm] = Fr(-1,2); gamE[Bm2] = Fr(1,4); gamE[Be] = Fr(-1,4)
def transpose(rep):
    lam, M, gam = rep
    return (gam[:], {ch: [list(r) for r in zip(*A)] for ch, A in M.items()}, lam[:])
Ep = transpose((lamE, {'0': M0, '1': M1}, gamE))   # now reads y MSB first

def dsum(r1, r2):
    l1, M1_, g1 = r1; l2, M2_, g2 = r2; d1, d2 = len(l1), len(l2)
    M = {}
    for ch in M1_:
        A = zeros(d1+d2, d1+d2)
        for i in range(d1):
            for j in range(d1): A[i][j] = M1_[ch][i][j]
        for i in range(d2):
            for j in range(d2): A[d1+i][d1+j] = M2_[ch][i][j]
        M[ch] = A
    return (l1 + l2, M, g1 + g2)
Slazy0 = dsum(Tp, Ep)

def leading_zeros(rep):
    lam, M, gam = rep; d = len(lam)
    M2 = {}
    A = zeros(d+1, d+1); A[0][0] = Fr(1)
    for i in range(d):
        for j in range(d): A[1+i][1+j] = M['0'][i][j]
    M2['0'] = A
    B = zeros(d+1, d+1)
    lm = [sum(lam[i]*M['1'][i][j] for i in range(d)) for j in range(d)]
    for j in range(d): B[0][1+j] = lm[j]
    for i in range(d):
        for j in range(d): B[1+i][1+j] = M['1'][i][j]
    M2['1'] = B
    return ([Fr(1)] + [Fr(0)]*d, M2, [ev(rep, '')] + gam[:])
Slazy = leading_zeros(Slazy0)

# ---------- Rel: pairs (x, y) aligned, x Zeckendorf (leading 1, no 11), y = 0^p lazy, val x = val y
# state: (a, b, xs, ys); the processed prefix has value difference e = a F_{j+1} + b F_j,
# j the number of digits still to read; reading digits (xd, yd) at position j gives
# e + (xd - yd) F_j = (a + b + xd - yd) F_j + a F_{j-1}.  At j = 0, e = a F_1 + b F_0 = a + b.
def rel_step(st, xd, yd, bound):
    a, b, xs, ys = st
    if xs == 'start' and xd != 1: return None
    if xs == 'last1' and xd == 1: return None
    xs2 = 'last1' if xd == 1 else 'last0'
    if ys == 'zeros': ys2 = 'last1' if yd == 1 else 'zeros'
    elif ys == 'last1': ys2 = 'last1' if yd == 1 else 'last0'
    else:
        if yd == 0: return None
        ys2 = 'last1'
    a2, b2 = a + b + (xd - yd), a
    if abs(a2) > bound or abs(b2) > bound: return None
    return (a2, b2, xs2, ys2)


def accepting(st):
    a, b, xs, ys = st
    return a + b == 0 and (xs != 'start' or ys == 'zeros')


def build_rel(bound):
    """Trimmed Rel: (list of states, transitions (i, xd, yd, j), accepting ids); state 0 is initial."""
    init = (0, 0, 'start', 'zeros')
    states = [init]; seen = {init: 0}; trans = []
    k = 0
    while k < len(states):
        st = states[k]
        for xd in (0, 1):
            for yd in (0, 1):
                t = rel_step(st, xd, yd, bound)
                if t is None: continue
                if t not in seen: seen[t] = len(states); states.append(t)
                trans.append((seen[st], xd, yd, seen[t]))
        k += 1
    co = {i for i, st in enumerate(states) if accepting(st)}
    changed = True
    while changed:
        changed = False
        for (i, xd, yd, j) in trans:
            if j in co and i not in co: co.add(i); changed = True
    keep = sorted(co)
    assert keep[0] == 0
    ren = {s: n for n, s in enumerate(keep)}
    trans2 = [(ren[i], xd, yd, ren[j]) for (i, xd, yd, j) in trans if i in co and j in co]
    return [states[i] for i in keep], trans2, [ren[i] for i in keep if accepting(states[i])]


REL_STATES, trans2, accR = build_rel(12)
nR = len(REL_STATES)
ren = {0: 0}

# ---------- product: series over x
dS = len(Slazy[0])
D = nR * dS
def pidx(r, s): return r*dS + s
MX = {}
for xc in '01':
    A = zeros(D, D)
    for (i, xd, yd, j) in trans2:
        if str(xd) != xc: continue
        My = Slazy[1][str(yd)]
        for s in range(dS):
            row = My[s]
            for t in range(dS):
                if row[t]: A[pidx(i, s)][pidx(j, t)] += row[t]
    MX[xc] = A
lamX = [Fr(0)]*D
for s in range(dS): lamX[pidx(0, s)] = Slazy[0][s]
gamX = [Fr(0)]*D
for r in accR:
    for s in range(dS): gamX[pidx(r, s)] = Slazy[2][s]
SX = (lamX, MX, gamX)



# ---------- checks
def tr1(w):
    return len(w) - len(w.rstrip("1"))


def lazy_table(maxlen):
    lz = {}
    for l in range(0, maxlen + 1):
        for x in ([0] if l == 0 else range(2 ** (l - 1), 2 ** l)):
            w = "" if l == 0 else bin(x)[2:]
            if "00" in w:
                continue
            v = sum(F[l - i] for i, ch in enumerate(w) if ch == "1")
            assert v not in lz
            lz[v] = w
    return lz


def check_components():
    allw = [""] + [bin(x)[2:] for x in range(1, 2 ** 10)]
    okW = all(ev(W, w) == (tr1(w) if in_L(w) else 0) for w in allw)
    pref, s = {}, 0
    for w in L_words(11):
        pref[w] = s
        s += tr1(w)
    okT = all(ev(T, u) == pref[u] for u in allw if "00" not in u)
    lz = lazy_table(17)
    okE = all(ev(Ep, lz[n]) == end_phase_splits(lz[n][:-1], int(lz[n][-1])) for n in range(1, 800))
    # the counter's stopping word and leftover ones form lazy(n)
    words = L_words(16)
    vals = [sum(F[len(w) + 1 - i] for i, ch in enumerate(w) if ch == "1") for w in words]
    okLazy = True
    j = 0
    for n in range(1, 2000):
        while vals[j] < n - 1:
            j += 1
        if words[j] + str(n - vals[j]) != lz[n]:
            okLazy = False
    return okW, okT, okE, okLazy


def check_rel_sound(maxlen=10):
    """Every accepted aligned pair has equal values, and (Zeck(n), lazy(n)) is accepted."""
    acc = set(accR)
    def accepts(x, y):
        cur = {0}
        for xd, yd in zip(x, y):
            cur = {j for (i, a, b, j) in trans2 if i in cur and a == int(xd) and b == int(yd)}
        return bool(cur & acc)
    lz = lazy_table(maxlen + 1)
    for l in range(1, maxlen + 1):
        for xv in range(2 ** (l - 1), 2 ** l):
            x = bin(xv)[2:]
            if "11" in x:
                continue
            vx = sum(F[l - i] for i, ch in enumerate(x) if ch == "1")
            for yv in range(2 ** l):
                y = bin(yv)[2:].zfill(l)
                if accepts(x, y) != (y.lstrip("0") == lz[vx]):
                    return False
    return True


def check_rel_complete():
    """Subset construction: every Zeckendorf word lies in the x-projection of Rel."""
    acc = set(accR)
    zdfa = {("z", "1"): "L1", ("L1", "0"): "L0", ("L0", "0"): "L0", ("L0", "1"): "L1"}
    start = ("z", frozenset({0}))
    seen = {start}
    stack = [start]
    while stack:
        zq, S = stack.pop()
        if not (S & acc):
            return False          # a Zeckendorf word (zq accepting: all states are) with no lazy partner
        for xd in "01":
            zq2 = zdfa.get((zq, xd))
            if zq2 is None:
                continue
            S2 = frozenset(j for (i, a, b, j) in trans2 if i in S and a == int(xd))
            st = (zq2, S2)
            if st not in seen:
                seen.add(st)
                stack.append(st)
    return True


def nine_dim_letter_rep(path, perturb=False):
    rep = json.loads(Path(path).read_text())
    C = {k: [[Fr(z) for z in r] for r in v] for k, v in rep["C"].items()}
    if perturb:
        C["10"][1][2] += 1
    x0 = [Fr(z) for z in rep["x0"]]; fE = [Fr(z) for z in rep["fE"]]; f1 = [Fr(z) for z in rep["f1"]]
    d = len(x0); D_ = 1 + 2 * d
    M0 = zeros(D_, D_); M1 = zeros(D_, D_)
    for i in range(d):
        M1[0][1 + d + i] = x0[i]
        M1[1 + i][1 + d + i] = Fr(1)
        for j in range(d):
            M0[1 + i][1 + j] += C["0"][i][j]
            M0[1 + d + i][1 + j] += C["10"][i][j]
    lam = [Fr(1)] + [Fr(0)] * (2 * d)
    gam = [sum(x0[i] * fE[i] for i in range(d))] + fE + f1
    return (lam, {"0": M0, "1": M1}, gam), (C, x0, fE, f1)


def equivalent(r1, r2):
    lam, M, gam = dsum(r1, (r2[0], r2[1], [-g for g in r2[2]]))
    n = len(lam)
    basis, piv = [], []
    queue = [lam]
    while queue:
        v = queue.pop()
        for b, p in zip(basis, piv):
            if v[p]:
                c = v[p] / b[p]
                v = [vi - c * bi for vi, bi in zip(v, b)]
        p = next((i for i in range(n) if v[i]), None)
        if p is None:
            continue
        if sum(v[i] * gam[i] for i in range(n)) != 0:
            return False
        basis.append(v); piv.append(p)
        nz = [i for i in range(n) if v[i]]
        for ch in "01":
            queue.append([sum(v[i] * M[ch][i][j] for i in nz) for j in range(n)])
    return True


def block_law_and_closed_forms(C, x0, fE, f1):
    d = len(x0)
    def mv(A, v): return [sum(A[i][j] * v[j] for j in range(d)) for i in range(d)]
    def vm(v, A): return [sum(v[i] * A[i][j] for i in range(d)) for j in range(d)]
    def dot(a, b): return sum(p * q for p, q in zip(a, b))
    A0, A10 = C["0"], C["10"]
    C02 = [[sum(A0[i][k] * A0[k][j] for k in range(d)) for j in range(d)] for i in range(d)]
    def span(vectors, ops):
        basis, piv, queue = [], [], list(vectors)
        while queue:
            v = queue.pop()
            for b, p in zip(basis, piv):
                if v[p]:
                    c = v[p] / b[p]; v = [x - c * y for x, y in zip(v, b)]
            p = next((i for i in range(len(v)) if v[i]), None)
            if p is None:
                continue
            basis.append(v); piv.append(p)
            for op in ops:
                queue.append(op(v))
        return basis
    # stacked columns (V(m), C0^{|m|} fE) over block words m, then words starting with block 10, and m = "1"
    Sall = span([fE + fE, f1 + mv(A0, fE)],
                [lambda w: mv(A0, w[:d]) + mv(A0, w[d:]), lambda w: mv(A10, w[:d]) + mv(C02, w[d:])])
    cols = [[a - b for a, b in zip(mv(A10, w[:d]), mv(C02, w[d:]))] for w in Sall]
    cols.append([a - b for a, b in zip(f1, mv(A0, fE))])
    r = vm(x0, A10)
    r = [a - b for a, b in zip(vm(vm(r, A0), A0), r)]          # x0 C10 (C0^2 - I)
    rows = span([r], [lambda v: vm(v, A0)])                     # times C0^{g-1}, all g >= 1
    block_ok = all(dot(k, c) == 0 for k in rows for c in cols)
    def S_rep(word):
        last1 = word.endswith("1"); body = word[:-1] if last1 else word
        x = x0[:]; i = 0
        while i < len(body):
            b = "10" if body[i] == "1" else "0"; x = vm(x, C[b]); i += len(b)
        return dot(x, f1 if last1 else fE)
    def closed(k):
        j = k - 1
        return F[k + 1] - Fr(2 * j * j + 8 * j + 15 + (-1) ** j, 8)
    okF = all(S_rep("1" + "0" * (k - 1)) == closed(k) for k in range(2, 41))
    okFm1 = all(S_rep(("10" * k)[:k - 1]) == closed(k) for k in range(2, 41))
    return block_ok, okF, okFm1


def main():
    here = Path(__file__).resolve().parent
    okW, okT, okE, okLazy = check_components()
    rel40 = build_rel(40)
    sx_ok = all(ev(SX, zeck(n)) == play(n, "SS")[2] for n in range(0, 601))
    nine, parts = nine_dim_letter_rep(here / "ss_linrep.json")
    bad, _ = nine_dim_letter_rep(here / "ss_linrep.json", perturb=True)
    block_ok, okF, okFm1 = block_law_and_closed_forms(*parts)
    gates = {
        "COMPONENT_W": okW,
        "COMPONENT_T": okT,
        "COMPONENT_E": okE,
        "LAZY_IS_STOP": okLazy,
        "REL_SOUND_len_le_10": check_rel_sound(),
        "REL_COMPLETE": check_rel_complete(),
        "REL_BOUND_STABLE": rel40[0] == REL_STATES and sorted(rel40[1]) == sorted(trans2),
        "SX_MATCHES_GAME_n_le_600": sx_ok,
        "EQUIVALENT_TO_9DIM": equivalent(SX, nine),
        "BLOCK_LAW": block_ok,
        "CLOSED_FORM_F_k": okF,
        "CLOSED_FORM_F_k_minus_1": okFm1,
        "CONTROL_perturbed_9dim_not_equivalent": not equivalent(SX, bad),
    }
    out = {
        "schema": "cbmd.deterministic-zeckendorf.ss-regularity.v1",
        "dimensions": {"W": dW, "T": dT, "S_lazy": dS, "Rel_states": nR, "SX": D},
        "rel_states": [list(s) for s in REL_STATES],
        "gates": gates,
        "status": "PASS" if all(gates.values()) else "FAIL",
        "nonclaims": ["the regularity proof is computer-assisted and rests on the written exact formula (§4)"],
        "authority_effect": "NONE",
    }
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
