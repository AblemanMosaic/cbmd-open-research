# Revisions

| Version | Change |
|---|---|
| 0.1.0 | Conjectured answer to BKR Question 6.11. Written proofs of the reductions, real monotonicity (Lemma 2), the `SU(2) → SO(3)` order formula `|K(γ)| = 2^{u−1}|G̃^{ab}|` (Proposition 3) and the orthogonal 3-dimensional classification (Theorem 4). Exact computation for the primitive subgroups of `SL_3(ℂ)`. Exhaustive SmallGroups and ATLAS scans. |
| 0.2.0 | Applied the independent review of 0.1.0. Wording: no-trivial-constituent hypothesis, `m ≥ 3` odd, invariance of `K` under relabelling, and the mechanism of (∗). Added the computer-assisted classification for `n = 3` (Theorem 9): Lemma 6 (abelian product bound), Theorem 7 (monomial types C, D: analytic reduction to diagonal part of order ≤ 75, then exact enumeration), Theorem 8 (reducible type B: central-factor bound, dihedral reduction, 18 exceptional groups). The conjecture is now stated for `n ≥ 4` only (Conjecture 10). GAP scripts now put the trivial character first explicitly; the old scripts stopped (fail-closed) on `S_5`, where GAP lists it elsewhere. Evidence coverage restated accurately: `n ≤ 6` up to order 71, not 150. |
