"""Chip-firing on the quadrant Z_{>=0}^2 (Inagaki-Khovanova-Luo, arXiv:2601.09125): small exact
gates for their Conjecture 7.3 and the thin-row lemma (pure Python).

Model: the Hasse diagram of Z_{>=0}^2 (edges (x,y)->(x+1,y), (x,y)->(x,y+1)); N chips at the
origin; a vertex with >= 2 chips fires one chip to each child.  F(x,y) = number of chips passing
through (x,y) satisfies F(0,0) = N, F(x,y) = floor(F(x-1,y)/2) + floor(F(x,y-1)/2).  Row i is the
antidiagonal x + y = i and len(i) its number of nonzero F entries (IKL Section 6.2).  The bottom
triangle is the largest set of final rows in which each row has one fewer entry than the previous
one (IKL Section 7).  Conjecture 7.3 (for N = 2^n): the number of rows in the bottom triangle equals
the length of the longest row minus 1.

A row (f_0..f_{L-1}) is *thin* if f_k <= 2 min(k, L-1-k) + 1 for all k.

Gates (each required):
  * CALIBRATION: N = 2^9 gives 92 nonzero rows (IKL Example 5) with longest row 13 and a long
    stretch alternating 12, 13 (IKL Section 6.2 reports 57 such rows; our maximal alternating
    stretch has 59 rows, 12 at both ends -- the paper's 'rectangle' is informal, so only the
    lengths 12/13 are calibrated); total firings T(10) = 38570 (IKL Section 3);
  * CONJ_7_3_POWERS: Conjecture 7.3 for N = 2^n, 1 <= n <= 18;
  * CONJ_7_3_ALL_N: the same statement for every N in 2..3000 (generalisation; observation);
  * THIN_LEMMA: (proved, argument section 2) the image g of a thin row of length L >= 2 has
    g_0 = g_L = 0 and g_x <= 2 min(x-1, L-1-x) + 1; checked on 20000 random thin rows, together with
    the consequence on every thin row of F for N <= 3000 (next row thin and one shorter), and a
    control showing the no-zero hypothesis is needed;
  * THIN_STRUCTURE: for every N in 4..3000 the first thin row has maximal length, is entered by a
    length increase, and all later rows are thin (observation; implies Conjecture 7.3 together
    with Prop 6.2 and the final row having length 2);
  * EVIDENCE_SUMMARY: evidence/quadrant_scans.json records no failure for N = 2^n, n <= 34, and for
    all N <= 300000.
"""
from __future__ import annotations
import json
import os
import random
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
EVIDENCE = os.path.normpath(os.path.join(HERE, '..', '..', 'evidence'))


def step(row):
    nxt = [(row[x - 1] // 2 if x >= 1 else 0) + (row[x] // 2 if x < len(row) else 0) for x in range(len(row) + 1)]
    lo = 0
    while lo < len(nxt) and nxt[lo] == 0:
        lo += 1
    hi = len(nxt) - 1
    while hi >= lo and nxt[hi] == 0:
        hi -= 1
    return nxt[lo:hi + 1]


def rows_of(N):
    out = []
    row = [N]
    while row:
        out.append(row)
        row = step(row)
    return out


def thin(row):
    L = len(row)
    return all(row[k] <= 2 * min(k, L - 1 - k) + 1 for k in range(L))


def triangle_rows(lens):
    r = len(lens) - 1
    while r > 0 and lens[r - 1] == lens[r] + 1:
        r -= 1
    return len(lens) - r


def conj_ok(N):
    R = rows_of(N)
    lens = [len(r) for r in R]
    no_gap = all(all(v > 0 for v in r) for r in R)
    steps = all(abs(lens[i + 1] - lens[i]) == 1 for i in range(len(lens) - 1))
    return triangle_rows(lens) == max(lens) - 1 and no_gap and steps


def main():
    results = {}
    R9 = rows_of(512)
    lens9 = [len(r) for r in R9]
    alt = 0
    best = 0
    for i in range(len(lens9)):
        if lens9[i] in (12, 13) and (alt == 0 or lens9[i] != lens9[i - 1]):
            alt += 1
        else:
            alt = 1 if lens9[i] in (12, 13) else 0
        best = max(best, alt)
    T10 = sum(v // 2 for r in rows_of(1024) for v in r)
    # IKL Example 5 partitions the n = 9 array as 10 + 13 + 57 + 12 = 92: top triangle, middle top,
    # "rectangular shape with 57 rows that alternate between 12 and 13, starting with 12", bottom
    # triangle.  Reproduce all four summands.  The bottom triangle (maximal final run of unit drops)
    # begins at the LAST longest row, so it shares its first two rows with the maximal alternating
    # stretch: that is why the stretch has 59 rows where IKL's rectangle has 57.
    bs = len(lens9) - 1
    while bs > 0 and lens9[bs - 1] - lens9[bs] == 1:
        bs -= 1
    last_longest = max(i for i, v in enumerate(lens9) if v == max(lens9))
    top9 = next(i for i in range(1, len(lens9)) if lens9[i] != i + 1)        # lengths 1, 2, 3, ...
    rect9 = best - 2
    mid9 = len(lens9) - top9 - rect9 - (len(lens9) - bs)
    ikl_partition = (top9, mid9, rect9, len(lens9) - bs) == (10, 13, 57, 12)
    rect_start_12 = lens9[bs - rect9] == 12 and lens9[bs - 1] == 12
    results['CALIBRATION'] = {'pass': len(R9) == 92 and max(lens9) == 13 and best == 59 and T10 == 38570
                              and bs == last_longest and ikl_partition and rect_start_12,
                              'rows_n9': len(R9), 'alternating_stretch_n9': best, 'T10': T10,
                              'ikl_partition_n9': [top9, mid9, rect9, len(lens9) - bs],
                              'bottom_triangle_starts_at_last_longest_row': bs == last_longest,
                              'rectangle_starts_with_12': rect_start_12}

    bad = [n for n in range(1, 19) if not conj_ok(2 ** n)]
    results['CONJ_7_3_POWERS'] = {'pass': not bad, 'n_range': [1, 18], 'failures': bad}

    bad = [N for N in range(2, 3001) if not conj_ok(N)]
    results['CONJ_7_3_ALL_N'] = {'pass': not bad, 'N_range': [2, 3000], 'failures': bad[:10]}

    rng = random.Random(1)
    lem_bad = 0
    control_found = False
    for _ in range(20000):
        L = rng.randint(2, 30)
        row = [rng.randint(1, 2 * min(k, L - 1 - k) + 1) for k in range(L)]
        g = [(row[x - 1] // 2 if x >= 1 else 0) + (row[x] // 2 if x < L else 0) for x in range(L + 1)]
        if g[0] != 0 or g[L] != 0 or any(g[x] > 2 * min(x - 1, L - 1 - x) + 1 for x in range(1, L)):
            lem_bad += 1
        img = step(row)
        if img and not thin(img):
            control_found = True  # trimming after interior zeros can break thinness
    f_rows = 0
    for N in range(4, 3001):
        R = rows_of(N)
        for a, b in zip(R, R[1:]):
            if thin(a):
                f_rows += 1
                if not (thin(b) and len(b) == len(a) - 1):
                    lem_bad += 1
    results['THIN_LEMMA'] = {'pass': lem_bad == 0 and control_found, 'random_rows': 20000,
                             'thin_rows_of_F_checked': f_rows, 'no_zero_hypothesis_needed_control': control_found}

    bad = []
    for N in range(4, 3001):
        R = rows_of(N)
        lens = [len(r) for r in R]
        t = next((i for i, r in enumerate(R) if thin(r)), None)
        ok = (t is not None and lens[t] == max(lens) and (t == 0 or lens[t - 1] == lens[t] - 1)
              and all(thin(r) for r in R[t:]) and lens[-1] == 2)
        if not ok:
            bad.append(N)
    results['THIN_STRUCTURE'] = {'pass': not bad, 'N_range': [4, 3000], 'failures': bad[:10]}

    ev = json.load(open(os.path.join(EVIDENCE, 'quadrant_scans.json')))
    ok = ev['powers_of_two']['failures'] == 0 and ev['powers_of_two']['n_max'] >= 34 \
        and ev['all_N']['failures'] == 0 and ev['all_N']['N_max'] >= 300000
    results['EVIDENCE_SUMMARY'] = {'pass': ok}

    allp = all(v['pass'] for v in results.values())
    for k, v in results.items():
        print(k, 'PASS' if v['pass'] else 'FAIL')
    if '--write' in sys.argv:
        with open(os.path.join(EVIDENCE, 'check_quadrant.json'), 'w') as fh:
            json.dump({'schema': 'cbmd.quadrant.check.v1', 'gates': results, 'pass': allp}, fh, indent=1)
            fh.write('\n')
    print('ALL PASS' if allp else 'FAILURES')
    return 0 if allp else 1


if __name__ == '__main__':
    sys.exit(main())
