# The ballot conjecture for labeled chip-firing on trees: counterexamples

## The model

The model is labeled chip-firing on the infinite undirected `k`-ary tree with a
self-loop at the root (Musiker–Nguyen 2023; Inagaki–Khovanova–Luo, Ann. Comb.
30 (2026), arXiv 2410.00039; Inagaki–Lin, arXiv 2509.17358).

- It starts from `N = (k^ℓ − 1)/(k − 1)` chips labeled `1, …, N` on the root.
- A vertex with at least `k + 1` chips may fire. It chooses any `k + 1` of its
  chips and sorts them.
  - The `⌈(k+1)/2⌉`-th smallest goes to the parent; the root keeps it.
  - The others go, in increasing order, to children `1, …, k`.
- The process is not confluent. Every stable configuration has exactly one
  chip on each vertex of the first `ℓ` levels.

**The ballot property.** For every vertex `v`, every pair of children
`a < b` and every `i`: the `i`-th smallest chip in the subtree of child `a` is
smaller than the `i`-th smallest chip in the subtree of child `b`.

- Inagaki, Khovanova and Luo conjecture it for every stable configuration on
  the binary tree, for the whole tree and every subtree. That is Conjecture
  3.7 on arXiv and Conjecture 3.16 in the published version.
- Their "ballot bound" (Theorem 3.19) on the number of stable configurations
  assumes this conjecture.
- Inagaki and Lin conjecture the `k`-ary version (Conjecture 5.1, `k ≥ 2`).
- Both were checked only at `ℓ = 3, 4` (binary, 15 chips).

## Results

**Theorem 1 (counterexamples).** The ballot property fails for some stable
configuration in each of these cases:

- `(k, ℓ) = (2, 5)`, with 31 chips, both at a subtree and at the root;
- `(2, 6)` and `(2, 7)`, at the root;
- `(3, 4)` (40 chips) and `(4, 4)` (85 chips), at the root.

So Conjecture 3.16 / 3.7 of Inagaki–Khovanova–Luo is false, and so is
Conjecture 5.1 of Inagaki–Lin (for `k = 2, 3, 4`). The ballot bound of
Inagaki–Khovanova–Luo loses its justification for `ℓ ≥ 5`.

*Proof.* Each case is an explicit firing sequence in
`verification/reference/counterexamples.json`. Each firing lists the vertex
and the `k + 1` chips it fires. The checker `check_ballot.py` replays each
sequence from scratch under the rules above. It checks that every firing is
legal, that the end is stable with the expected shape, and that the ballot
property fails.

The 31-chip example with a root violation ends in this configuration, level by
level:

```
[23]
[20, 27]
[12, 24, 16, 29]
[2, 13, 11, 25, 6, 21, 18, 30]
[1, 4, 5, 19, 10, 14, 15, 28, 3, 8, 9, 26, 7, 22, 17, 31]
```

The left subtree of the root holds `1, 2, 4, 5, 10, …` and the right subtree
holds `3, 6, 7, 8, 9, …`. Their 5th smallest chips are `10 > 9`. ∎

**Theorem 2 (where the property holds).** For `(k, ℓ) ∈ {(2, ≤ 4), (3, ≤ 3),
(4, ≤ 3)}`, every stable configuration has the ballot property.

*Proof.*

- **Threshold reduction.** For sets `A`, `B` of equal size, "`i`-th smallest
  of `A` < `i`-th smallest of `B` for every `i`" is equivalent to
  "`|A ∩ [1, t]| ≥ |B ∩ [1, t]|` for every `t`" (gate
  `THRESHOLD_EQUIVALENCE`).
- **Two-colour projection.** Colour the chips `≤ t` red. A firing of `k + 1`
  chips containing `r` reds sends red exactly to the positions of rank `≤ r` in
  sorted order, so the coloured state (reds and blues per vertex) evolves by a
  finite-choice rule.
  - Every labeled run projects to a coloured run.
  - Every coloured run lifts to a labeled one, by choosing any chips of the
    right colours.
- **Exhaustive search.** For each `t`, an exhaustive search of all coloured
  runs finds red-count dominance at every vertex in every stable coloured
  state (gate `POSITIVE_CASES`). ∎

For `(2, 4)` this independently confirms the published 15-chip check, which
relied on Liscio's list of 36,220 configurations. The same projection found
the counterexamples:

- the exhaustive search at `(2, 5)` reaches stable coloured states that
  violate the property from `t = 8` (`evidence/colour_exhaustive_binary_l5.json`);
- a randomized coloured search found the others;
- each was lifted to labels.

Uniformly random labeled firing missed them: no violation appeared in 200,000
runs at `(2, 5)`. The violations need deliberately extreme choices of chips.

## Not claimed

- Failure for every `ℓ ≥ 5` (or `ℓ ≥ 4` for `k ≥ 3`). Only the listed cases
  are certified.
- Whether the ballot bound's numbers are still valid upper bounds.
- The number of stable configurations at `ℓ ≥ 5`.
