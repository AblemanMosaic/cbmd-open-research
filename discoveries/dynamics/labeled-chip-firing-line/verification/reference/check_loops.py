"""Labeled chip-firing on Z with loops and parallel edges (HMP Conjectures 21 and 25): exact
small-case gates, pure Python.

Model (Hopkins-McConville-Propp, Sorting via chip-firing, EJC 24(3) 2017, Section 3).
Z<S> is the path Z with one loop added at each i in S; r(G) replaces every edge (loops
included) by r parallel copies.  A site v with l_v left edges, m_v loops and r_v right edges
fires by choosing l_v + m_v + r_v of its chips: the l_v smallest labels move left, the r_v
largest move right, the m_v middle ones stay.  G "sorts" Delta^n (chips 1..n at 0) if every
stable D reachable from Delta^n has D(i) <= D(j) for all i <= j.

Two-colour reduction.  For a threshold t colour chips 1..t red and t+1..n blue.  Every labeled
run projects to a colour run (which chips move left/stay/right depends only on how many reds
are chosen), and every colour run lifts to a labeled run (choose any reds and blues with the
required counts).  A labeled stable state is sorted iff for every t its projection has no blue
chip strictly left of a red chip.  Hence: G sorts Delta^n  <=>  for every t in 1..n-1 no
reachable stable colour state has a blue chip strictly left of a red chip.

Conjecture 21 condition ("QUAL"): the unlabeled stabilization of n chips at 0 strictly extends
that of n-1 chips on both ends.

Gates (each required):
  * TWO_COLOUR_EQUALS_LABELED: the two-colour test agrees with a direct labeled exhaustive
    search for r = 1, all S in [-2,2] with |S| <= 2 and n <= 7, and r = 2, S in [-1,1], n <= 4;
  * CONTROL_HMP_EVEN_ODD: Z (S empty) sorts Delta^n exactly for even n, 2 <= n <= 10 (HMP
    Theorem; the odd cases must FAIL, so the test is not vacuous);
  * KL_ALL_LOOPS: with a loop at every site in reach, the QUAL n in 3..11 are exactly
    n = 3 mod 4, and they sort (Klivans-Liscio Theorem 3.13);
  * KL_PARALLEL: 2Z sorts Delta^4, Delta^8 and 3Z sorts Delta^6 (HMP Conjecture 24, proved by
    Klivans-Liscio Theorem 3.2); 2Z does not sort Delta^6 (control);
  * CONJ21_SMALL: every QUAL instance with S in [-3,3], |S| <= 3, n <= 10 sorts;
  * CONJ25_SMALL: every QUAL instance with S in [-2,2], |S| <= 2, n <= 6 sorts under r = 2;
  * SCALING_SMALL: for S in [-2,2], |S| <= 2, 2 <= n <= 6, r(Z<S>) sorts Delta^{rn} for r = 2
    iff Z<S> sorts Delta^n (observation, not a theorem);
  * CONVERSE_SMALL: for S in [-3,3], |S| <= 3 and 3 <= n <= 9 with the origin able to fire,
    every non-QUAL instance FAILS to sort (observation, not a theorem);
  * EVIDENCE_SUMMARY: the recorded C++ scan summaries in evidence/loops_scans.json report no
    exception (all QUAL instances sort; all scanned non-QUAL instances fail; no scaling mismatch).
"""
from __future__ import annotations
import itertools
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EVIDENCE = os.path.normpath(os.path.join(HERE, '..', '..', 'evidence'))


def stab_support(n, S):
    """Support (min, max) of the unlabeled stabilization of n chips at 0 on Z<S>."""
    c = {0: n}
    while True:
        moved = False
        for v in sorted(c):
            d = 3 if v in S else 2
            if c[v] >= d:
                k = c[v] // d
                c[v] -= k * d
                if v in S:
                    c[v] += k
                c[v - 1] = c.get(v - 1, 0) + k
                c[v + 1] = c.get(v + 1, 0) + k
                moved = True
        if not moved:
            occ = [v for v, x in c.items() if x]
            return min(occ), max(occ)


def qual(n, S):
    a = stab_support(n, S)
    b = stab_support(n - 1, S)
    return a[0] < b[0] and a[1] > b[1]


def sorts_two_colour(n, S, r=1):
    """True iff r(Z<S>) sorts Delta^n, by the two-colour reduction."""
    for t in range(1, n):
        start = ((0, t, n - t),)
        seen = {start}
        stack = [start]
        while stack:
            s = stack.pop()
            cfg = {p: (R, B) for p, R, B in s}
            fired = False
            for v, (R, B) in cfg.items():
                m = r if v in S else 0
                d = 2 * r + m
                if R + B < d:
                    continue
                fired = True
                for k in range(max(0, d - B), min(d, R) + 1):
                    u = dict(cfg)
                    kl = min(k, r)
                    km = min(max(k - r, 0), m)
                    kr = max(k - r - m, 0)
                    R0, B0 = u[v]
                    u[v] = (R0 - k + km, B0 - (d - k) + (m - km))
                    Rl, Bl = u.get(v - 1, (0, 0))
                    u[v - 1] = (Rl + kl, Bl + r - kl)
                    Rr, Br = u.get(v + 1, (0, 0))
                    u[v + 1] = (Rr + kr, Br + r - kr)
                    key = tuple(sorted((p, a, b) for p, (a, b) in u.items() if a or b))
                    if key not in seen:
                        seen.add(key)
                        stack.append(key)
            if not fired:
                blue = False
                for p, R, B in s:  # s is sorted by position
                    if R and blue:
                        return False
                    if B:
                        blue = True
    return True


def sorts_labeled(n, S, r=1):
    """Direct labeled exhaustive search (small n only)."""
    start = tuple([0] * n)
    seen = {start}
    stack = [start]
    while stack:
        s = stack.pop()
        at = {}
        for i, p in enumerate(s):
            at.setdefault(p, []).append(i)
        fired = False
        for v, chips in at.items():
            m = r if v in S else 0
            d = 2 * r + m
            if len(chips) < d:
                continue
            fired = True
            for choice in itertools.combinations(chips, d):  # chips are increasing labels
                u = list(s)
                for j, c in enumerate(choice):
                    u[c] = v - 1 if j < r else (v + 1 if j >= r + m else v)
                u = tuple(u)
                if u not in seen:
                    seen.add(u)
                    stack.append(u)
        if not fired:
            if any(s[i] > s[i + 1] for i in range(n - 1)):
                return False
    return True


def subsets(lo, hi, maxsize):
    for size in range(maxsize + 1):
        for S in itertools.combinations(range(lo, hi + 1), size):
            yield frozenset(S)


def main():
    results = {}

    bad = []
    count = 0
    for S in subsets(-2, 2, 2):
        for n in range(2, 8):
            count += 1
            if sorts_two_colour(n, S) != sorts_labeled(n, S):
                bad.append((sorted(S), n, 1))
    for S in subsets(-1, 1, 3):
        for n in range(2, 5):
            count += 1
            if sorts_two_colour(2 * n, S, 2) != sorts_labeled(2 * n, S, 2):
                bad.append((sorted(S), n, 2))
    results['TWO_COLOUR_EQUALS_LABELED'] = {'pass': not bad, 'cases': count, 'mismatches': bad}

    obs = {n: sorts_two_colour(n, frozenset()) for n in range(2, 11)}
    results['CONTROL_HMP_EVEN_ODD'] = {'pass': all(obs[n] == (n % 2 == 0) for n in obs),
                                        'sorts': {str(n): obs[n] for n in obs}}

    ALL = frozenset(range(-12, 13))
    q = [n for n in range(3, 12) if qual(n, ALL)]
    srt = {n: sorts_two_colour(n, ALL) for n in q}
    results['KL_ALL_LOOPS'] = {'pass': q == [n for n in range(3, 12) if n % 4 == 3] and all(srt.values()),
                               'qual_n': q, 'sorts': {str(n): srt[n] for n in q}}

    kp = {'2Z_4': sorts_two_colour(4, frozenset(), 2), '2Z_8': sorts_two_colour(8, frozenset(), 2),
          '3Z_6': sorts_two_colour(6, frozenset(), 3), '2Z_6_control': sorts_two_colour(6, frozenset(), 2)}
    results['KL_PARALLEL'] = {'pass': kp['2Z_4'] and kp['2Z_8'] and kp['3Z_6'] and not kp['2Z_6_control'],
                              'values': kp}

    tested = 0
    fails = []
    for S in subsets(-3, 3, 3):
        for n in range(2, 11):
            if qual(n, S):
                tested += 1
                if not sorts_two_colour(n, S):
                    fails.append((sorted(S), n))
    results['CONJ21_SMALL'] = {'pass': not fails and tested > 0, 'qual_instances': tested, 'failures': fails}

    tested = 0
    fails = []
    for S in subsets(-2, 2, 2):
        for n in range(2, 7):
            if qual(n, S):
                tested += 1
                if not sorts_two_colour(2 * n, S, 2):
                    fails.append((sorted(S), n))
    results['CONJ25_SMALL'] = {'pass': not fails and tested > 0, 'qual_instances': tested, 'failures': fails}

    mism = []
    count = 0
    for S in subsets(-2, 2, 2):
        for n in range(2, 7):
            count += 1
            if sorts_two_colour(n, S) != sorts_two_colour(2 * n, S, 2):
                mism.append((sorted(S), n))
    results['SCALING_SMALL'] = {'pass': not mism, 'cases': count, 'mismatches': mism}

    tested = 0
    exceptions = []
    for S in subsets(-3, 3, 3):
        for n in range(max(3, 3 if 0 in S else 2), 10):
            if not qual(n, S):
                tested += 1
                if sorts_two_colour(n, S):
                    exceptions.append((sorted(S), n))
    results['CONVERSE_SMALL'] = {'pass': not exceptions and tested > 0, 'nonqual_instances': tested,
                                 'exceptions': exceptions}

    ev = json.load(open(os.path.join(EVIDENCE, 'loops_scans.json')))
    ok = (ev['conjecture_21']['non_ok'] == 0 and ev['conjecture_25_r2']['non_ok'] == 0
          and ev['conjecture_25_r3']['non_ok'] == 0 and ev['converse']['sorting_without_condition'] == 0
          and ev['scaling']['mismatches'] == 0)
    results['EVIDENCE_SUMMARY'] = {'pass': ok}

    all_pass = all(v['pass'] for v in results.values())
    for k, v in results.items():
        print(k, 'PASS' if v['pass'] else 'FAIL')
    out = {'schema': 'cbmd.labeled-line.loops-check.v1', 'gates': results, 'pass': all_pass}
    if '--write' in sys.argv:
        with open(os.path.join(EVIDENCE, 'check_loops.json'), 'w') as f:
            json.dump(out, f, indent=1)
            f.write('\n')
    print('ALL PASS' if all_pass else 'FAILURES')
    return 0 if all_pass else 1


if __name__ == '__main__':
    sys.exit(main())
