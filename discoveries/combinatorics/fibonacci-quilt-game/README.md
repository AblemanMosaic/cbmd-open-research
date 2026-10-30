# The Fibonacci Quilt game: a linear bound on game length

> **Standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-COMB-FQ-GAME-001`

## The question

The Fibonacci Quilt game (Miller and Newlon, Fibonacci Quart. 58 (2020);
arXiv 1909.01938) plays a Zeckendorf-type game with the quilt numbers
`1, 2, 3, 4, 5, 7, 9, 12, 16, …`, where `q_i = q_{i−2} + q_{i−3}`. Termination
is known, through a monovariant built from square roots of indices. The authors
ask: *"Is there a reasonable upper bound on the length of a game?"* They note
that simulations never gave a game near `2n`.

## What this dossier finds

- **A linear bound (proved, exact rational certificate).** Every game on `n`
  lasts at most `(23/10) n + 2.95` moves.
  - The proof is a potential function: explicit rational weights on indices
    below 31, and `u_i = 2.3 q_i − i/3 − β` above.
  - Every rule lowers the potential by at least 1, except rule 2(a), which is
    used at most once.
  - The finitely many small-index cases are checked in exact arithmetic; the
    rest reduce to four one-line inequalities.
- **The maximum exceeds `2n` (exhaustive).** The longest games for all
  `n ≤ 90`, about 11 million states, reach `2n` first at `n = 78`, and reach
  `2.022n` at `n = 89`.
- **The method's limit.** Potentials of this shape cannot beat about `2.29`.
  The per-`n` potential bound stays within 12 moves of the true maximum for
  `50 ≤ n ≤ 90`, which suggests the true constant is near `2.29`.
- **A printed rule is inconsistent.** Rule 3(f)'s second option, `q_3, q_7`,
  does not preserve value; this dossier reads it as `q_5, q_7`.

## What is not established

- The exact asymptotic constant of the longest game, or a strategy that
  attains it.
- Who wins (Miller–Newlon ask whether Player 2 still wins).
- An independent review.
- Novelty; see [`review/PRIOR_ART.md`](review/PRIOR_ART.md).

## Smallest decisive tests

- A rule instance that lowers the potential by less than 1. The checker scans
  every instance with indices `≤ 200` exactly, and the rest are covered
  analytically.
- A game longer than `2.3n + 2.95`.

## Reproduction

```text
python -B discoveries/combinatorics/fibonacci-quilt-game/verification/reference/fq_bound.py
c++ -O2 -o fqmax discoveries/combinatorics/fibonacci-quilt-game/verification/reference/fq_longest_exhaustive.cpp
./fqmax 90
```

## Repository map

- `argument/`: the written argument.
- `verification/reference/`: the exact checker, the potential, the optional
  LP and the exhaustive search.
- `evidence/`: check outputs.
- `review/`: prior art.
- `revisions/`: revision history.
