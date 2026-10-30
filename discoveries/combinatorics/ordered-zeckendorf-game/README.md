# The ordered Zeckendorf game: the Long Game Strategy's constant

> **Standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-COMB-ORDERED-ZECK-001`

## The question

The ordered Zeckendorf game (Bortnovskyi, Lucas, Miller, Vraneško, Watson and White, arXiv 2508.20222, 2025) plays
the Zeckendorf game on an ordered list that starts as `n` copies of `F_1 = 1`.
Merges and splits act on adjacent terms, and a *switch* swaps an adjacent
out-of-order pair. The longest game `M(n)` is quadratic. The authors prove
`M(n) = n²/2 − Θ(n log_φ n)`:

- the upper bound is `M(n) ≤ n²/2 − (1/32) n log_φ n`;
- the lower bound comes from their Long Game Strategy (LGS), with constant 1.

They conjecture that LGS is longest (Conjecture 1.7). In Remark 3.1 they
estimate from simulation that the constant in front of `n log_φ n` is "bigger
than 0.4 and much lower than 1".

## What this dossier finds

- **The LGS constant is `φ/√5` (proved, written).**
  `L_LGS(n) = n²/2 − (φ/√5) n log_φ n + O(n)`, and
  `φ/√5 = (5 + √5)/10 = 0.7236…` is the density of `1`s in lazy Fibonacci
  representations.
  - This improves the lower bound to `M(n) ≥ n²/2 − 0.7236… n log_φ n − O(n)`.
  - If Conjecture 1.7 holds, it is the limit of the ratio of Remark 3.1. That
    ratio converges slowly, like `κ − 4.17/log_φ n` (0.44 at `10³`, 0.63 at
    `2·10⁹`), which explains the authors' reading.
  - An exhaustive search confirms that LGS is longest for every `n ≤ 24`.
  - An independent review found the proof correct up to fixable gaps; the
    fixes are applied.
- **Why.**
  - Under LGS the list is always sorted before a non-switch move, so a move
    costs the inversions it creates.
  - After the ones are combined, a large pile of `2`s is drained. Each draining
    split sends an `F_1` across the pile.
  - Above the pile, the pieces run the same lazy Fibonacci counter as in Split
    Smallest.
  - An invariant (`U − 2P` counts the draining splits) turns the length deficit
    into the sum of the counter's digit sums, which grows like
    `(φ/√5) n log_φ n`.
- **Observed:** `(n²/2 − L)/n − (φ/√5) log_φ n` stays in `[−4.21, −4.06]` from
  `n = 10³` to `10⁹`.

## What is not established

- That LGS is the longest strategy (Conjecture 1.7).
- Any improvement to the upper bound's `1/32`.
- The winner of the ordered game.
- An independent review and a machine-checked proof.
- Novelty; see [`review/PRIOR_ART.md`](review/PRIOR_ART.md).

## Smallest decisive tests

- A rest moment whose upper word is not the next counter-language word.
- A step with a costly split above index 3.
- An `n` where `(n²/2 − L)/n − (φ/√5) log_φ n` drifts out of a bounded window.

## Reproduction

```text
python -B discoveries/combinatorics/ordered-zeckendorf-game/verification/reference/lgs_constant.py 600
cc -O2 -o lgs discoveries/combinatorics/ordered-zeckendorf-game/verification/reference/lgs_fast.c -lm
./lgs 1000 10000 100000 1000000 10000000 100000000 1000000000
```

## Repository map

- `argument/`: the written argument.
- `verification/reference/`: the gated checker and the C counter.
- `evidence/`: check outputs.
- `review/`: prior art.
- `revisions/`: revision history.
