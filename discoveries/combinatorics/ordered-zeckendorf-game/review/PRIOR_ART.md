# Prior art

- **Bortnovskyi, Lucas, Miller, Vraneško, Watson and White, *The Ordered Zeckendorf Game* (arXiv 2508.20222, 2025).**
  - They define the game and the Long Game Strategy.
  - They prove `M(n) ≤ n(n − 1)/2` and
    `M(n) ≤ n²/2 − (1/32) n log_φ n + o(n log n)`.
  - They prove that LGS takes at least `n²/2 − n log_φ n + o(n log n)` moves.
  - They conjecture that LGS is longest.
  - Their Remark 3.1 estimates the `n log_φ n` constant numerically at
    "bigger than 0.4 and much lower than 1".
- **The lazy Fibonacci counter and its language.** These are proved for Split
  Smallest in the sibling dossier `deterministic-zeckendorf-games` (§4).
- **The density.** The frequency of `1`s in Zeckendorf (golden-mean)
  representations is `1/(φ² + 1)`. Lazy representations are their complements,
  which gives `φ/√5`. This is standard.

Searches (October 2026) found no later work on the LGS constant. Not a novelty
determination.
