# Labeled chip-firing on the line, odd number of chips: evidence

> **Standing:** `CONJECTURE`, `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-DYN-LABELED-LINE-001`

## The question

Hopkins, McConville and Propp (*Sorting via chip-firing*, EJC 24(3) 2017)
study labeled chip-firing on `ℤ`. A site with two or more chips sends the
smaller of a chosen pair left and the larger right. With an even number of
chips the outcome is always sorted. With `n = 2m + 1` chips it is not, and two
of their conjectures remain open:

- **Conjecture 26:** the maximal number of inversions of an outcome is `m`
  (checked for `n ≤ 9`);
- **Conjecture 27:** under each of three random protocols, the probability of
  ending sorted tends to `1/3`.

## What this dossier records (evidence, no proof)

- **Conjecture 26 holds at `n = 11`.** The search covers 6,520,201 states and
  819 outcomes, and the maximal inversion count is 5.
- **Exact sorting probabilities for `n ≤ 11`** under protocols 1 (uniform over
  moves) and 2 (uniform unstable site, then uniform pair):

  | `n` | protocol 1 | protocol 2 |
  |---|---|---|
  | 3 | `1/3` | `1/3` |
  | 5 | `1/5` | `1/5` |
  | 7 | `0.2512` | `0.2501` |
  | 9 | `0.3147` | `0.3118` |
  | 11 | `0.3314` | `0.3305` |

  The values for `n ≤ 9` are exact rationals in `evidence/check_line.json`.
- **Monte Carlo up to `m = 80`.** At 20,000 runs per point, the estimates stay
  within 0.006 of `1/3`.

## What is not established

- Proofs of either conjecture.
- Protocol 3 (a uniformly random stabilization sequence).

## Reproduction

```text
python -B discoveries/dynamics/labeled-chip-firing-line/verification/reference/check_line.py
c++ -O2 -o zline discoveries/dynamics/labeled-chip-firing-line/verification/reference/zline.cpp && ./zline 11
c++ -O2 -o exactp discoveries/dynamics/labeled-chip-firing-line/verification/reference/exactp.cpp && ./exactp 11 2
```
