# Prior art

- **Bortnovskyi, Lucas, Miller, Vraneško, Watson and White, *The Ordered Zeckendorf Game* (arXiv 2508.20222, 2025).**
  - They define the game and the Long Game Strategy.
  - They prove `M(n) ≤ n(n − 1)/2` and
    `M(n) ≤ n²/2 − (1/32) n log_φ n + o(n log n)`.
  - They prove that LGS takes at least `n²/2 − n log_φ n + o(n log n)` moves.
  - They conjecture that LGS is longest.
  - Their Remark 3.1 estimates the `n log_φ n` constant numerically as at
    least `0.4` and "much lower that 1", and says their Theorems 1.10 and
    1.11 "contain too crude estimates to give an insight for the explicit
    constant". It also notes the `1/32` of Theorem 1.11 can be improved to
    `1/(8φ) ≈ 0.077`.
  - **Version check (audit, October 2026).** Remark 3.1 has the same number
    and the same content in v1 (August 2025) and v2 (March 2026), so the
    question is still posed in the current version. The near-identical
    Williams SMALL preprint has the passage without the `Remark 3.1` label.
  - **Consistency with their numerics.** The exact constant proved here,
    `φ/√5 = 0.7236…`, lies inside their bracket `[0.4, 1)`.
  - Their Theorem 1.10 is an LGS-specific lower bound, so the constant for
    LGS is a well-posed part of Remark 3.1. Pinning the constant for `M(n)`
    itself needs their Conjecture 1.7, which is why the claim here is
    conditional on it.
- **The lazy Fibonacci counter and its language.** These are proved for Split
  Smallest in the sibling dossier `deterministic-zeckendorf-games` (§4).
- **The density.** The frequency of `1`s in Zeckendorf (golden-mean)
  representations is `1/(φ² + 1)`. Lazy representations are their complements,
  which gives `φ/√5`. This is standard.

An independent literature audit (October 2026) found no later work
determining the constant: neither arXiv version, nor the Williams SMALL
preprint, nor the 2026 Miller-group Zeckendorf talks (CANT 2026, YMC 2026),
which do not treat the ordered variant. The audit could not reach citation
databases, so its sweep is search- and preprint-based rather than
index-complete, and it read the sources through a fetch layer that caps
verbatim quotation. Not a novelty determination.
