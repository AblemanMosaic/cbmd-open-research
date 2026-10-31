# Minimal critical groups of McKay quivers (BKR Question 6.11)

> **Standing:** `CONJECTURE`, `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-COMB-MCKAY-MIN-001`

## The question

For a faithful representation `γ : G ↪ SL_n(ℂ)` of a finite group, the
critical group `K(γ)` of the McKay quiver always surjects onto the dual of
`G^{ab}` (Benkart–Klivans–Reiner). When `n = 2` this map is an isomorphism.
BKR ask (Question 6.11) for which `γ` it is an isomorphism in general. Call
such `γ` *minimal*. Trivial summands do not matter, so assume there are none.

## What this dossier records

**Conjecture.** `γ` is minimal if and only if `n = 2`, or `n = 3` and `γ(G)`
is one of the following rotation groups acting on `ℂ³` without a fixed
vector:

- the dihedral group of order `2m` with `m` odd;
- `A_4`;
- `A_5`.

**Proved** (`argument/WRITTEN_ARGUMENT.md`):

- **Proposition 3.** For `G ⊂ SO(3)` with preimage `G̃ ⊂ SU(2)`,
  `|K(γ)| = 2^{u−1} |G̃^{ab}|`, where `u` counts the classes of `G̃` that
  equal their negatives. The proof uses the factorisation
  `3 − χ_γ = (2 − χ_ρ)(2 + χ_ρ)` on `G̃`, Gaetz's order formula and the
  `n = 2` theorem.
- **Theorem 4.** It settles every orthogonal 3-dimensional case, which is
  the same as every case with `n = 3` and real-valued character:
  - minimal: cyclic groups, dihedral groups of order `2m` with `m` odd,
    `A_4` and `A_5`;
  - not minimal: dihedral groups with `m` even, where `|K| = 16` versus
    `|G^{ab}| = 4`;
  - not minimal: `S_4`, where `|K| = 4` versus `|G^{ab}| = 2`.
- **Lemma 2.** For real characters, adding a nontrivial summand of
  determinant 1 strictly enlarges `|K|`.
- **Proposition 5.** An exact computation from character tables for all
  eight primitive subgroup types of `SL_3(ℂ)`. Only `A_5` is minimal. For
  example, Klein's group `PSL(2,7)` has `K ≅ ℤ/2`.

**Checked**, with no exception:

- exhaustive scans of GAP's SmallGroups library, covering every faithful
  representation into `SL_n` without trivial constituent:
  - all groups of order ≤ 40 with `n ≤ 5`: 380,521 representations;
  - all non-abelian groups of order ≤ 150 except 128, with `n ≤ 6`;
- 47 ATLAS character tables with `n ≤ 8`.

In all of these the minimal representations are exactly the conjectured
ones, and nothing violates the BKR surjection. No minimal case with
`n ≥ 4` was found.

## What is not established

- The conjecture for `n = 3` with a non-real character (monomial or
  reducible), and for all `n ≥ 4`.
- Specialist review of the written arguments.
- **Prior art.** BKR's Proposition 6.19 (the abelian case) and the rest of
  their Section 6 could not be fully read here. BKR already list `A_4` as a
  minimal example with `n = 3`. See `review/PRIOR_ART.md`.
- Structural statements beyond orders. Examples: `K ≅ (ℤ/4)²` for dihedral
  groups with `m` even, and `K ≅ ℤ/4` for `S_4`. These are computed for
  `m ≤ 30` only.

## Reproduction

Needs GAP 4 with SmallGrp and CTblLib.

```text
python -B discoveries/combinatorics/mckay-critical-group-minimal/verification/reference/check_mckay_minimal.py
```

The large scans are listed in `verification/reference/README.md`.
