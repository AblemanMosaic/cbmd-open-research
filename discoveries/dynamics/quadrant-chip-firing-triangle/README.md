# Chip-firing on the quadrant: the bottom-triangle conjecture checked to 2^34 chips

> **Standing:** `CONJECTURE`, `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-DYN-QUADRANT-TRIANGLE-001`

## The question

Inagaki, Khovanova and Luo (arXiv:2601.09125) study chip-firing on the
directed quadrant `ℤ²_{≥0}` with `2^n` chips at the origin. A vertex with at
least two chips sends one chip to each of its two children. Let `F(x, y)` be
the number of chips that pass through `(x, y)`. The length of an antidiagonal
row is its number of nonzero `F` values.

The final rows of `F` form a "bottom triangle": each row has one fewer entry
than the previous one. IKL's **Conjecture 7.3** says that the bottom triangle
has exactly (length of the longest row) − 1 rows. They checked it for
`n ≤ 12`.

## What this dossier records

- **Conjecture 7.3 holds for every `n ≤ 34`.** The largest case is
  `N = 2^34`: 9,276,188 rows, longest row 3,648, bottom triangle 3,647 rows.
  The computation is the exact row recursion `F'(x) = ⌊F(x−1)/2⌋ + ⌊F(x)/2⌋`
  in 64-bit integers.
- **The same statement holds for every chip count `2 ≤ N ≤ 300,000`**, not
  only powers of 2. This is an observation; the conjecture asks only about
  `2^n`.
- **A proved lemma** (`argument/WRITTEN_ARGUMENT.md`, §2). Call a row *thin*
  if its `k`-th entry from the nearer end is at most `2k + 1`. Once a row of
  `F` is thin, every later row is thin and one entry shorter.
- **Where a proof would come from.** The conjecture would follow from the
  observed statement (S): the first thin row is a longest row, it is entered
  by a length increase, and the last row has length 2. (S) holds for every
  scanned `N`.
- **Calibration against the paper.**
  - `n = 9` gives 92 rows, as in IKL Example 5.
  - `T(10) = 38,570` total firings, as in IKL §3.
  - IKL describe a "rectangle" of 57 rows alternating 12 and 13. Our longest
    alternating stretch has 59 rows. The paper does not define the
    rectangle, so we calibrate only the lengths 12 and 13.

## What is not established

- A proof of Conjecture 7.3 or of (S).
- Any `N` beyond the stated ranges.

## Reproduction

```text
python -B discoveries/dynamics/quadrant-chip-firing-triangle/verification/reference/check_quadrant.py
cc -O2 -o quadscan discoveries/dynamics/quadrant-chip-firing-triangle/verification/reference/quadscan.c
./quadscan 17179869184 17179869184     # N = 2^34, about 1 minute
./quadscan 2 300000                    # every N up to 300,000, about 2 minutes
```
