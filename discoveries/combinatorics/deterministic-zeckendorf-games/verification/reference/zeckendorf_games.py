"""Deterministic Zeckendorf games: lengths, the add-move correction, and regularity.

Rules (Baird-Smith, Epstein, Flint, Miller 2018): start from n copies of F_1 = 1
(indexing F_1 = 1, F_2 = 2, F_3 = 3, ...). A move is
  * add 1's:          F_1, F_1  -> F_2
  * add consecutive:  F_{i-1}, F_i -> F_{i+1}           (i >= 2)
  * split:            F_2, F_2 -> F_1, F_3 ;  F_i, F_i -> F_{i-2}, F_{i+1} (i >= 3)
The game ends at the Zeckendorf decomposition of n. The four deterministic games
of Li, Li, Miller et al. (Fibonacci Quart. 58 (2020)) fix a priority order:
  CL  add consecutive (largest first), add 1's, split (largest first)
  SL  split (largest first), add consecutive (largest first), add 1's
  CS  add 1's, add consecutive (smallest first), split (smallest first)
  SS  split (smallest first), add 1's, add consecutive (smallest first)

Gates (each required):
  * MERGES: every game makes exactly n - Z(n) merging moves (add 1's or add
    consecutive), so the length is n - Z(n) + #splits;
  * LENGTH_IDENTITY: for every game, L = sum_{i in Zeck(n)} c_i - sum over add-
    consecutive moves of (j - 2), j the index produced, where c_1 = 0, c_2 = 1,
    c_3 = 3 and c_{i+1} = 2 c_i - c_{i-2} + 1 (a potential argument; the c_i are
    the longest-game weights);
  * KNOWN: CL and SL have length n - Z(n) (Li et al., Theorem 1.3);
  * LONGEST: SS attains the maximum game length over all play, computed by
    dynamic programming over the full game graph (Cusenza et al. 2021,
    Theorem 1.2), for small n;
  * SS_REPRESENTATION: the 9-dimensional linear representation in
    ss_linrep.json, read over the Zeckendorf blocks {0, 10} with a final 1,
    reproduces the split count of SS for every n in range (the representation
    was fitted on prefixes of length <= 10 and suffixes of length <= 8,
    i.e. words of length <= 18, and is tested far beyond);
  * SS_FIBONACCI: S_SS(F_k) = F_{k+1} - (2k^2 + 8k + 15 + (-1)^k)/8, k >= 1
    (indexing F_0 = 1, F_1 = 2), and S_SS(F_k - 1) = S_SS(F_k);
  * SS_BLOCKS: S_SS(F_k + m) - S_SS(F_k) - S_SS(m) depends only on m and the
    parity of k, for k >= 4 and m < F_{k-1};
  * CS_NOT_LOW_RANK: the Hankel matrices of the CS split count over Zeckendorf
    words have full rank 13, 21, 34 at prefix/suffix length 6, 7, 8 (evidence
    that CS is not Fibonacci-regular of small rank; not a proof);
  * COUNTER: while at least two 1's remain, SS inserts a 2 and normalises by
    splits; the normalised upper part (indices >= 2, index 2 rightmost) runs
    through exactly the binary words with no "00" except one final "00" followed
    only by 1's, in increasing order, and each step makes as many splits as the
    previous word has trailing 1's (checked for 20,000 steps; proved in the
    written argument);
  * END_PHASE: from a lazy word w (indices >= 2, index 2 rightmost) with
    a in {0,1} ones, SS makes sum over blocks of 1's, right to left, of
    floor((k - 1 + g)^2 / 4) splits, with carry g = a if w ends in 1 else 0
    initially and g <- [k + g >= 2] after each block (all lazy words of
    length <= 14; proved in the written argument);
  * EXACT_FORMULA: S_SS(n) = (sum of trailing-1 counts over the words of the
    counter language before w*) + END_PHASE(w*, n - value(w*)), w* the first
    counter word of value >= n - 1, matches simulation for every n in range;
  * CONTROL: perturbing one entry of the SS representation breaks agreement.
"""
from __future__ import annotations

import itertools
import json
import sys
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

HERE = Path(__file__).resolve().parent
N_MAX = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 3000

FIB = [1, 2]
while len(FIB) < 80:
    FIB.append(FIB[-1] + FIB[-2])


def zeck_indices(n):
    """1-based indices of the Zeckendorf terms of n (F_1 = 1, F_2 = 2, ...)."""
    out = []
    for i in range(len(FIB) - 1, -1, -1):
        if FIB[i] <= n:
            out.append(i + 1)
            n -= FIB[i]
    return out


def play(n, game):
    """Return (length, merges, splits, adds) where adds lists produced indices."""
    c = [n]
    merges = splits = 0
    adds = []

    def ensure(k):
        while len(c) <= k:
            c.append(0)

    def do_ones():
        if c[0] >= 2:
            ensure(1)
            c[0] -= 2
            c[1] += 1
            return True
        return False

    def do_add(largest):
        idx = range(len(c) - 1, 0, -1) if largest else range(1, len(c))
        for i in idx:
            if c[i - 1] > 0 and c[i] > 0:
                ensure(i + 1)
                c[i - 1] -= 1
                c[i] -= 1
                c[i + 1] += 1
                adds.append(i + 2)
                return True
        return False

    def do_split(largest):
        idx = range(len(c) - 1, 0, -1) if largest else range(1, len(c))
        for i in idx:
            if c[i] >= 2:
                ensure(i + 1)
                c[i] -= 2
                c[i + 1] += 1
                c[0 if i == 1 else i - 2] += 1
                return True
        return False

    order = {
        "CL": [("A", True), ("O", None), ("S", True)],
        "SL": [("S", True), ("A", True), ("O", None)],
        "CS": [("O", None), ("A", False), ("S", False)],
        "SS": [("S", False), ("O", None), ("A", False)],
    }[game]
    while True:
        moved = False
        for kind, largest in order:
            if kind == "O" and do_ones():
                merges += 1
                moved = True
            elif kind == "A" and do_add(largest):
                merges += 1
                moved = True
            elif kind == "S" and do_split(largest):
                splits += 1
                moved = True
            if moved:
                break
        if not moved:
            break
    final = [i + 1 for i, x in enumerate(c) for _ in range(x)]
    return merges + splits, merges, splits, adds, sorted(final, reverse=True)


C_WEIGHT = [None, 0, 1, 3]
while len(C_WEIGHT) < 80:
    i = len(C_WEIGHT) - 1
    C_WEIGHT.append(2 * C_WEIGHT[i] - C_WEIGHT[i - 2] + 1)


# ----- all moves, for the longest-game DP -----
def moves(s):
    s = list(s)
    out = []

    def norm(t):
        while t and t[-1] == 0:
            t.pop()
        return tuple(t)
    for i in range(len(s)):
        if s[i] >= 2:
            t = s + [0, 0]
            t[i] -= 2
            if i == 0:
                t[1] += 1
            elif i == 1:
                t[0] += 1
                t[2] += 1
            else:
                t[i - 2] += 1
                t[i + 1] += 1
            out.append(norm(t))
        if i >= 1 and s[i - 1] > 0 and s[i] > 0:
            t = s + [0, 0]
            t[i - 1] -= 1
            t[i] -= 1
            t[i + 1] += 1
            out.append(norm(t))
    return out


@lru_cache(None)
def longest(s):
    ms = moves(s)
    return 0 if not ms else 1 + max(longest(t) for t in ms)


# ----- Zeckendorf words and the SS representation -----
def to_word(n):
    if n == 0:
        return ""
    k = max(i for i in range(len(FIB)) if FIB[i] <= n)
    w = ""
    for i in range(k, -1, -1):
        if FIB[i] <= n:
            w += "1"
            n -= FIB[i]
        else:
            w += "0"
    return w


def word_value(w):
    m = len(w)
    return sum(FIB[m - 1 - i] for i, ch in enumerate(w) if ch == "1")


def load_rep(path):
    r = json.loads(path.read_text(encoding="utf-8"))
    C = {k: [[Fraction(z) for z in row] for row in v] for k, v in r["C"].items()}
    return C, [Fraction(z) for z in r["x0"]], [Fraction(z) for z in r["fE"]], [Fraction(z) for z in r["f1"]]


def rep_eval(rep, n):
    C, x0, fE, f1 = rep
    w = to_word(n)
    last1 = w.endswith("1")
    body = w[:-1] if last1 else w
    x = x0[:]
    i = 0
    while i < len(body):
        blk = "10" if body[i] == "1" else "0"
        x = [sum(x[a] * C[blk][a][b] for a in range(len(x))) for b in range(len(x))]
        i += len(blk)
    vec = f1 if last1 else fE
    return sum(x[a] * vec[a] for a in range(len(x)))


def rank(M):
    M = [[Fraction(x) for x in row] for row in M]
    r = 0
    cols = len(M[0]) if M else 0
    for col in range(cols):
        p = next((i for i in range(r, len(M)) if M[i][col] != 0), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        for i in range(len(M)):
            if i != r and M[i][col] != 0:
                f = M[i][col] / M[r][col]
                M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        r += 1
    return r


def hankel_rank(S, length):
    words = ["".join(b) for b in itertools.product("01", repeat=length) if "11" not in "".join(b)]
    U = [u for u in words if u.endswith("0")]
    M = [[S[word_value(u + v)] for v in words] for u in U]
    return rank(M)


def counter_check(steps=20000):
    c = [10 ** 9]
    words, split_counts = [], []
    splits = 0

    def ensure(k):
        while len(c) <= k:
            c.append(0)
    while len(words) < steps:
        moved = False
        for i in range(1, len(c)):
            if c[i] >= 2:
                ensure(i + 1)
                c[i] -= 2
                c[i + 1] += 1
                c[0 if i == 1 else i - 2] += 1
                splits += 1
                moved = True
                break
        if moved:
            continue
        if any(x > 1 for x in c[1:]):
            return False
        words.append("".join(str(x) for x in reversed(c[1:])).lstrip("0"))
        split_counts.append(splits)
        splits = 0
        c[0] -= 2
        ensure(1)
        c[1] += 1

    def in_language(w):
        i = w.find("00")
        return i < 0 or set(w[i + 2:]) <= {"1"}
    top = int(words[-1], 2)
    expected = [""] + [format(x, "b") for x in range(1, top + 1) if in_language(format(x, "b"))]
    if expected != words:
        return False
    for t in range(1, len(words)):
        prev = words[t - 1]
        trailing = len(prev) - len(prev.rstrip("1"))
        if split_counts[t] != trailing:
            return False
    return True


def end_phase_splits(w, a):
    blocks = [len(b) for b in reversed(w.split("0")) if b]
    g = a if w.endswith("1") else 0
    total = 0
    for k in blocks:
        total += ((k - 1 + g) ** 2) // 4
        g = 1 if k + g >= 2 else 0
    return total


def upper_value(w):
    m = len(w)
    return sum(FIB[m - i] for i, ch in enumerate(w) if ch == "1")


def ss_from_state(a, w):
    """Run SS from a ones and upper word w; return the number of splits."""
    c = [a] + [int(ch) for ch in reversed(w)]
    splits = 0

    def ensure(k):
        while len(c) <= k:
            c.append(0)
    while True:
        moved = False
        for i in range(1, len(c)):
            if c[i] >= 2:
                ensure(i + 1)
                c[i] -= 2
                c[i + 1] += 1
                c[0 if i == 1 else i - 2] += 1
                splits += 1
                moved = True
                break
        if moved:
            continue
        if c[0] >= 2:
            ensure(1)
            c[0] -= 2
            c[1] += 1
            continue
        for i in range(1, len(c)):
            if c[i - 1] > 0 and c[i] > 0:
                ensure(i + 1)
                c[i - 1] -= 1
                c[i] -= 1
                c[i + 1] += 1
                moved = True
                break
        if not moved:
            return splits


def end_phase_check(max_len=14):
    for L in range(1, max_len + 1):
        for bits in itertools.product("01", repeat=L):
            w = "".join(bits)
            if not w.startswith("1") or "00" in w:
                continue
            for a in (0, 1):
                if ss_from_state(a, w) != end_phase_splits(w, a):
                    return False
    return True


def exact_formula(n_max):
    def in_language(w):
        i = w.find("00")
        return i < 0 or set(w[i + 2:]) <= {"1"}
    seq = []
    x = 0
    cum = 0
    while True:
        w = format(x, "b") if x else ""
        x += 1
        if not in_language(w):
            continue
        v = upper_value(w) if w else 0
        seq.append((w, v, cum))
        cum += len(w) - len(w.rstrip("1"))
        if v > n_max + 2:
            break
    out = {}
    j = 0
    for n in range(1, n_max + 1):
        while seq[j][1] < n - 1:
            j += 1
        w, v, c = seq[j]
        out[n] = c + end_phase_splits(w, n - v)
    return out


def main():
    counts = {}
    S = {g: {0: 0} for g in ("CL", "SL", "CS", "SS")}
    merges_ok = identity_ok = known_ok = True
    for n in range(1, N_MAX + 1):
        Z = zeck_indices(n)
        for g in S:
            L, mg, sp, adds, final = play(n, g)
            S[g][n] = sp
            if final != Z or mg != n - len(Z):
                merges_ok = False
            if L != sum(C_WEIGHT[i] for i in Z) - sum(j - 2 for j in adds):
                identity_ok = False
            if g in ("CL", "SL") and L != n - len(Z):
                known_ok = False
    longest_ok = all(play(n, "SS")[0] == longest((n,)) for n in range(1, 41))
    rep = load_rep(HERE / "ss_linrep.json")
    rep_bad = [n for n in range(1, N_MAX + 1) if rep_eval(rep, n) != S["SS"][n]]
    # control: perturb one representation entry
    C, x0, fE, f1 = rep
    C2 = {k: [row[:] for row in v] for k, v in C.items()}
    C2["10"][1][2] += 1
    control_bites = any(rep_eval((C2, x0, fE, f1), n) != S["SS"][n] for n in range(1, N_MAX + 1))
    fib_ok = True
    for k in range(1, len(FIB)):
        if FIB[k] > N_MAX:
            break
        target = FIB[k + 1] - Fraction(2 * k * k + 8 * k + 15 + (-1) ** k, 8)
        if S["SS"][FIB[k]] != target or S["SS"][FIB[k] - 1] != S["SS"][FIB[k]]:
            fib_ok = False
    blocks = {}
    blocks_ok = True
    for k in range(4, len(FIB)):
        if FIB[k] > N_MAX:
            break
        for m in range(FIB[k - 1]):
            n = FIB[k] + m
            if n > N_MAX:
                break
            d = S["SS"][n] - S["SS"][FIB[k]] - S["SS"][m]
            key = (k % 2, m)
            if key in blocks and blocks[key] != d:
                blocks_ok = False
            blocks[key] = d
    hank = {g: [hankel_rank(S[g], L) for L in (6, 7, 8)] for g in ("SS", "CS")}
    counts.update(n_max=N_MAX, ss_rep_mismatches=len(rep_bad), hankel_ranks=hank,
                  cs_length_ratio_at_n_max=play(N_MAX, "CS")[0] / N_MAX,
                  ss_length_ratio_at_n_max=play(N_MAX, "SS")[0] / N_MAX)
    gates = {
        "MERGES_n_minus_Z": merges_ok,
        "LENGTH_IDENTITY": identity_ok,
        "KNOWN_CL_SL_length_n_minus_Z": known_ok,
        "LONGEST_SS_is_maximum_n_le_40": longest_ok,
        "SS_REPRESENTATION_exact": not rep_bad,
        "SS_FIBONACCI_closed_form": fib_ok,
        "SS_BLOCKS_parity_law": blocks_ok,
        "CS_NOT_LOW_RANK_evidence": hank["CS"] == [13, 21, 34],
        "SS_LOW_RANK": max(hank["SS"]) <= 9,
        "CONTROL_perturbed_representation_fails": control_bites,
        "COUNTER_lazy_language_radix_order": counter_check(),
        "END_PHASE_block_formula": end_phase_check(),
        "EXACT_FORMULA_matches_simulation": all(v == S["SS"][n] for n, v in exact_formula(N_MAX).items()),
    }
    out = {"schema": "cbmd.deterministic-zeckendorf.v1", "counts": counts, "gates": gates,
           "status": "PASS" if all(gates.values()) else "FAIL",
           "nonclaims": ["SS regularity is proved in ss_regularity.py; this script checks the representation in range",
                         "CS non-regularity is evidenced by Hankel rank growth, not proved"],
           "authority_effect": "NONE"}
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
