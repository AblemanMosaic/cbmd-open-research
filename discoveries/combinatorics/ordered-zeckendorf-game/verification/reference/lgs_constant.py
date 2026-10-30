"""The Long Game Strategy of the ordered Zeckendorf game: L = n^2/2 - (phi/sqrt5) n log_phi n + O(n).

Game (Bortnovskyi, Lucas, Miller, Vraneško, Watson, White, arXiv 2508.20222): an ordered list of n copies of F_1 = 1
(F_2 = 2, F_{k+1} = F_k + F_{k-1}). Moves: merge an adjacent (F_i, F_{i+1}) into
F_{i+2}; merge (F_1, F_1) into F_2; split an adjacent (F_i, F_i), i > 2, into
(F_{i-2}, F_{i+1}); split (F_2, F_2) into (F_1, F_3); switch an adjacent
(F_i, F_j) with i > j. Long Game Strategy (LGS), in priority order: switches;
combine adjacent ones from the left; splits from the right; merges from the left.

Gates (each required):
  * COUNT_MODEL: the count dynamics (sorted list, cost = inversions created)
    equals direct list simulation of LGS for every n <= 40;
  * NO_MERGE_IN_PILE_PHASE: while c_2 >= 2 there is no merge other than ones;
  * UPPER_SPLITS_FREE: every split at an index >= 4 during the pile phase has
    c_{j-1} = 0 and c_j = 2 (so it creates no inversion), and every split at
    index 3 has c_3 = 2;
  * STEP_LEMMA: at the moments before each split at index 2, the pieces at
    indices >= 3 (index 3 rightmost) run through the counter language L
    (binary words with no 00 except one final 00 followed only by 1's) in
    increasing order, and each step makes 1 + [word ends in 1] expensive
    splits (at index 2 or 3);
  * INVARIANT_Q: during the pile phase U - 2P = number of expensive splits so
    far (U = value at indices >= 3, P = number of pieces there);
  * EXACT_IDENTITY: n^2/2 - L = sum_k P_k + R with the closed form
    R = -n/4 + r^2/4 + (e + e^2)/4 + sum_k c1_k/2 + 2 s2 - moves - tail
    (r = n mod 2, e = n - E), for every n in range;
  * DENSITY: over lazy words of length l (leading 1, no 00), and over all
    counter-language words of length l, the number of 1's T and its
    (1 + [ends in 1])-weighted version satisfy |T - (phi/sqrt5) l N| <= 2N
    (N the matching count), for l <= 60;
  * WINDOW: (n^2/2 - L)/n - (phi/sqrt5) log_phi n lies in [-5, -3] for
    200 <= n <= N_MAX and at n = 10^4, 10^5;
  * CONTROL: replacing phi/sqrt5 by 0.65 or 0.80 makes that quantity drift by
    more than 0.3 between n = 10^3 and n = 10^5 (it drifts by less than 0.2
    with phi/sqrt5).
"""
from __future__ import annotations
import json
import math
import sys
from decimal import Decimal, getcontext

N_MAX = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 600
F = [0, 1, 2]
while len(F) < 120:
    F.append(F[-1] + F[-2])
PHI = (1 + 5 ** 0.5) / 2
KAPPA = PHI / 5 ** 0.5


def direct_lgs(n):
    a = [1] * n
    L = 0
    while True:
        p = next((p for p in range(len(a) - 1) if a[p] > a[p + 1]), None)
        if p is not None:
            a[p], a[p + 1] = a[p + 1], a[p]; L += 1; continue
        p = next((p for p in range(len(a) - 1) if a[p] == 1 and a[p + 1] == 1), None)
        if p is not None:
            a[p:p + 2] = [2]; L += 1; continue
        p = next((p for p in range(len(a) - 2, -1, -1) if a[p] == a[p + 1] and a[p] >= 2), None)
        if p is not None:
            i = a[p]; a[p:p + 2] = [1, 3] if i == 2 else [i - 2, i + 1]; L += 1; continue
        p = next((p for p in range(len(a) - 1) if a[p + 1] == a[p] + 1), None)
        if p is not None:
            a[p:p + 2] = [a[p] + 2]; L += 1; continue
        return L


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


def count_lgs(n, checks=False, words=None):
    """Count-model LGS. Returns dict of totals; with checks, verifies the lemmas."""
    c = [0] * 120
    c[1] = n
    L = 0
    while c[1] >= 2:
        L += 1 + c[1] - 2; c[1] -= 2; c[2] += 1
    phase1, m, r = L, c[2], c[1]
    E = s2 = moves = 0
    sumP = sumc1 = 0
    ok = {"merge": True, "upper": True, "step": True, "Q": True}
    rest = []
    step_exp = []
    cur_exp = 0
    def word():
        return "".join(str(x) for x in c[3:]).rstrip("0")[::-1]
    while c[2] >= 2 or c[1] >= 2:
        moves += 1
        if c[1] >= 2:
            L += 1 + c[1] - 2; c[1] -= 2; c[2] += 1; continue
        j = next((i for i in range(118, 1, -1) if c[i] >= 2), None)
        if j is None:
            ok["merge"] = False
            break
        U = sum(c[i] * F[i] for i in range(3, 120)); P = sum(c[3:])
        if checks and U - 2 * P != E:
            ok["Q"] = False
        if j == 2:
            if checks:
                rest.append(word())
                if rest[:-1]:
                    step_exp.append(cur_exp)
                cur_exp = 0
            E += 1; s2 += 1; cur_exp += 1; sumP += P; sumc1 += c[1]
            L += 1 + c[2] - 2; c[2] -= 2; c[1] += 1; c[3] += 1
        elif j == 3:
            if c[3] != 2:
                ok["upper"] = False
            E += 1; cur_exp += 1; sumP += P; sumc1 += c[1]
            L += 1 + c[2] + c[3] - 2; c[3] -= 2; c[1] += 1; c[4] += 1
        else:
            if c[j - 1] != 0 or c[j] != 2:
                ok["upper"] = False
            L += 1 + c[j - 1] + c[j] - 2; c[j] -= 2; c[j - 2] += 1; c[j + 1] += 1
    pile_L = L - phase1
    while True:
        if c[1] >= 2:
            L += 1 + c[1] - 2; c[1] -= 2; c[2] += 1; continue
        j = next((i for i in range(118, 1, -1) if c[i] >= 2), None)
        if j:
            L += 1 + (c[2] - 2 if j == 2 else c[j - 1] + c[j] - 2)
            c[j] -= 2; c[j + 1] += 1; c[1 if j == 2 else j - 2] += 1; continue
        i0 = next((i for i in range(1, 118) if c[i] and c[i + 1]), None)
        if i0:
            L += 1 + c[i0 + 1] - 1; c[i0] -= 1; c[i0 + 1] -= 1; c[i0 + 2] += 1; continue
        break
    tail_L = L - phase1 - pile_L
    if checks:
        if words is None:
            words = L_words(max(len(w) for w in rest) + 1)
        ok["step"] = rest == words[:len(rest)] and all(
            e == 1 + (w.endswith("1")) for w, e in zip(rest, step_exp))
    return dict(L=L, phase1=phase1, m=m, r=r, E=E, s2=s2, moves=moves, sumP=sumP,
                sumc1=sumc1, tail=tail_L, ok=ok)


def exact_identity(n, d):
    """n^2/2 - L = sum_k P_k + R with R in closed form (written argument §3)."""
    from fractions import Fraction
    E, r = d["E"], d["r"]
    e = n - E
    R = (Fraction(-n, 4) + Fraction(r * r, 4) + Fraction(e + e * e, 4)
         + Fraction(d["sumc1"], 2) + 2 * d["s2"] - d["moves"] - d["tail"])
    return Fraction(n * n, 2) - d["L"] == d["sumP"] + R


def Fraction_(a, b=1):
    from fractions import Fraction
    return Fraction(a, b)


def density_check(lmax=60):
    getcontext().prec = 60
    k = (1 + Decimal(5).sqrt()) / 2 / Decimal(5).sqrt()
    # automaton for words with leading 1; lazy: states 'A1','A0'; counter language adds 'B' (after the 00)
    def run(states, delta, accept):
        # vectors indexed by state: (count, ones)
        cnt = {s: 0 for s in states}; ones = {s: 0 for s in states}
        cnt["A1"] = 1; ones["A1"] = 1
        ok = True
        for l in range(1, lmax + 1):
            N = sum(cnt[s] for s in accept); T = sum(ones[s] for s in accept)
            last1 = [s for s in accept if s in ("A1", "B")]   # states whose last digit is 1 (B: last digit 1 or the 00 itself)
            Nw = N + sum(cnt[s] for s in ("A1",)) + sum(cnt[s] for s in ("B1",) if s in cnt)
            Tw = T + sum(ones[s] for s in ("A1",)) + sum(ones[s] for s in ("B1",) if s in ones)
            if abs(Decimal(T) - k * l * N) > 2 * N or abs(Decimal(Tw) - k * l * Nw) > 2 * Nw:
                ok = False
            c2 = {s: 0 for s in states}; o2 = {s: 0 for s in states}
            for s in states:
                for d in (0, 1):
                    t = delta.get((s, d))
                    if t is None:
                        continue
                    c2[t] += cnt[s]; o2[t] += ones[s] + d * cnt[s]
            cnt, ones = c2, o2
        return ok
    lazy = run(["A1", "A0"], {("A1", 1): "A1", ("A1", 0): "A0", ("A0", 1): "A1"}, ["A1", "A0"])
    # counter language: after the single 00 only 1's; B0 = just read the second 0, B1 = then 1's
    full = run(["A1", "A0", "B0", "B1"],
               {("A1", 1): "A1", ("A1", 0): "A0", ("A0", 1): "A1", ("A0", 0): "B0",
                ("B0", 1): "B1", ("B1", 1): "B1"},
               ["A1", "A0", "B0", "B1"])
    return lazy and full


def deficit(n):
    d = count_lgs(n)
    return (n * n / 2 - d["L"]) / n - KAPPA * math.log(n, PHI)


def main():
    count_ok = all(count_lgs(n)["L"] == direct_lgs(n) for n in range(1, 41))
    words = L_words(16)
    oks = {"merge": True, "upper": True, "step": True, "Q": True}
    ident = True
    window = True
    for n in range(2, N_MAX + 1):
        d = count_lgs(n, checks=True, words=words)
        for k2 in oks:
            oks[k2] &= d["ok"][k2]
        ident &= exact_identity(n, d)
        if n >= 200:
            q = (n * n / 2 - d["L"]) / n - KAPPA * math.log(n, PHI)
            window &= -5 <= q <= -3
    big = {n: deficit(n) for n in (1000, 10000, 100000)}
    window &= all(-5 <= v <= -3 for v in big.values())
    def drift(kap):
        vals = [(n * n / 2 - count_lgs(n)["L"]) / n - kap * math.log(n, PHI) for n in (1000, 100000)]
        return abs(vals[1] - vals[0])
    gates = {
        "COUNT_MODEL_n_le_40": count_ok,
        "NO_MERGE_IN_PILE_PHASE": oks["merge"],
        "UPPER_SPLITS_FREE": oks["upper"],
        "STEP_LEMMA": oks["step"],
        "INVARIANT_Q": oks["Q"],
        "EXACT_IDENTITY": ident,
        "DENSITY_l_le_60": density_check(),
        "WINDOW": window,
        "CONTROL_wrong_constants_drift": drift(KAPPA) < 0.2 and drift(0.65) > 0.3 and drift(0.80) > 0.3,
    }
    out = {
        "schema": "cbmd.ordered-zeckendorf.lgs-constant.v1",
        "n_max": N_MAX,
        "kappa": "phi/sqrt(5) = (5 + sqrt(5))/10 = %.12f" % KAPPA,
        "deficit_minus_kappa_log": {str(k): round(v, 4) for k, v in big.items()},
        "gates": gates,
        "status": "PASS" if all(gates.values()) else "FAIL",
        "nonclaims": ["the asymptotic is a written proof; LGS optimality (Conjecture 1.7) is not claimed"],
        "authority_effect": "NONE",
    }
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
