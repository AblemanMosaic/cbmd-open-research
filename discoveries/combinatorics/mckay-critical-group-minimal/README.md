# Minimal critical groups of McKay quivers (BKR Question 6.11)

> **Standing:** `CONJECTURE`, `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-COMB-MCKAY-MIN-001`

## The question

For a faithful representation `γ : G ↪ SL_n(ℂ)` of a finite group, the
critical group `K(γ)` of the McKay quiver always surjects onto the dual of
`G^{ab}` (Benkart–Klivans–Reiner). When `n = 2` this map is an isomorphism.
BKR ask (Question 6.11) for which `γ` it is an isomorphism in general. Call
such `γ` *minimal*. Trivial summands do not matter, so assume there are none.

C. Gaetz (honors thesis, 2016) listed the known minimal pairs. They are the
finite subgroups of `SL_2(ℂ)`, and the rotation groups `C_m`, `D_{2m}`
(`m` odd), `A_4`, `A_5` in `SO(3)`. He proved that list complete inside
`SO(3)`, and asked whether these pairs are the only ones (his Question 2).

## What this dossier records

**Theorem 9 (`n = 3`, computer-assisted; Gaetz's Question 2 in dimension
3).** A faithful `γ : G ↪ SL_3(ℂ)`
without trivial constituent is minimal if and only if `χ_γ` is real-valued
and `G` is one of:

- dihedral of order `2m` with `m ≥ 3` odd;
- `A_4`;
- `A_5`.

These are rotation groups in `SO(3)`.

**Conjecture 10 (Gaetz's Question 2 for `n ≥ 4`).** There is no minimal `γ`
with `n ≥ 4`. Together with BKR (`n = 2`) and Theorem 9, this would answer
Question 6.11 completely.

How Theorem 9 is proved (`argument/WRITTEN_ARGUMENT.md`), case by case
following Blichfeldt's classification of finite subgroups of `SL_3(ℂ)`:

- **Real characters: Proposition 3 and Theorem 4.** The classification is
  Gaetz's (Theorem 8(ii), case by case). What is new here is a uniform
  formula: for `G ⊂ SO(3)` with
  preimage `G̃ ⊂ SU(2)`, `|K(γ)| = 2^{u−1} |G̃^{ab}|`, where `u` counts the
  classes of `G̃` equal to their negatives. The proof uses
  `3 − χ_γ(πx) = (2 − χ_ρ(x))(2 − χ_ρ(−x))`, Gaetz's order formula and the
  `n = 2` theorem. The non-minimal rotation groups are:
  - dihedral with `m` even, where `|K| = 16` versus 4;
  - `S_4`, where `|K| = 4` versus 2.
- **Monomial groups (types C, D): Theorem 7.** Explicit lower bounds reduce
  everything to diagonal parts of order `≤ 75`, built on Lemma 6, a product
  bound from the abelian case. An exact enumeration of those groups (70 in
  normal form) leaves only `A_4` and `S_3 = D_6`.
- **Reducible groups (type B): Theorem 8.**
  - The centre contributes `z²|1 − (−2)^z|/3` to Gaetz's product, which
    bounds the centre.
  - The dihedral case reduces to order `≤ 46`, or to the real dihedral
    family.
  - The 18 exceptional groups (projective image `A_4`, `S_4`, `A_5`) are
    computed directly.
- **Primitive groups (types E–L): Proposition 5.** Exact computation for
  all eight. Only `A_5` is minimal; Klein's `PSL(2,7)` has `K ≅ ℤ/2`.
- **Abelian groups (type A):** `CBMD-COMB-CAYLEY-JAC-001`.

**Also proved: Theorem M (adding a summand enlarges `K`), with no
hypotheses.** For `γ_1` faithful and `γ_2` *any* representation of `G`,

    |K(γ_1 ⊕ γ_2)| ≥ |K(γ_1)|,

with equality exactly when `γ_2` is a multiple of the trivial
representation. So a minimal `γ` has no faithful proper summand once trivial
summands are deleted (Corollary M1), which is the reduction Gaetz's Question
2 needs; and for two faithful summands
`|K(γ_1 ⊕ γ_2)| ≥ |K(γ_1)| + |K(γ_2)|` (Corollary M2, attained already for
`G = ℤ/2`).

The route is the matrix-tree theorem rather than the sector geometry. The
McKay–Cartan matrix `nI − M` is not a digraph Laplacian — the McKay quiver's
out-degrees are not `n` — but conjugating by the diagonal matrix of
irreducible degrees makes it one, with arc weights `M_{ij} δ_j / δ_i`. So
`|K(γ)|` is a weighted count of arborescences of the McKay quiver pointing at
the trivial vertex (Lemma A); `M` is additive in `γ`, so the determinant
expands into a sum of non-negative mixed terms, one of which is `|K(γ_1)|`;
and strictness has a one-line witness, since a nontrivial constituent `χ_j`
of `γ_2` forces an arc from `χ_j^*` straight to the trivial vertex, and
swapping that arc into an arborescence of `Q(γ_1)` cannot create a cycle
because the arc ends at the root. On the way, the count rooted at `χ_v` turns
out to be `δ_v²` times the one at the trivial vertex, which re-proves the
order formula (F3) by elementary linear algebra (Proposition B).

This supersedes the earlier Lemma 2, which needed `det γ_1 = det γ_2 = 1`
together with "`χ_1` real-valued or `1/n_1 + 1/n_2 ≥ 1/2`" and rested on a
sector lemma: for `U ∈ SU(n)`, `n − tr U` lies in `|arg| ≤ π/2 − π/n`. The
sector lemma is kept as an independent statement. The 1,359,437-pair search
that found no violation without the dimension condition (non-abelian groups
of order ≤ 60, dimensions ≤ 4) is now explained, including its zero
equalities: that scan excluded multiples of the trivial character from
`γ_2`, which is exactly the equality case.

**No novelty is claimed for Lemma A, Proposition B or Theorem M.** One
source, Grinberg–Huang–Reiner (arXiv:1704.03778), could plausibly contain
them — the proofs use only facts that have Hopf-algebra analogues there —
and its text past the middle of §6 cannot be retrieved by the fetch tools.
They are recorded as proved, not as new; see `review/PRIOR_ART.md`.

**Checked**, with no exception. The scans cover every faithful
representation into `SL_n` without trivial constituent, from GAP's
SmallGroups library:

- all groups of order ≤ 40 with `n ≤ 5`;
- non-abelian groups of order ≤ 71 with `n ≤ 6`;
- non-abelian groups of order ≤ 150 with `n = 3`;
- non-abelian groups of order 72–150 with `n ≤ 4` (so every non-abelian
  group of order ≤ 150 is covered for `n ≤ 4`);
- 47 ATLAS character tables with `n ≤ 8`.

No minimal case with `n ≥ 4` was found.

## What is not established

- Conjecture 10 (`n ≥ 4`).
- Specialist review. Two independent agent reviews found no mathematical
  error:
  - of Lemmas 1–2 (the real case), Proposition 3 and Theorem 4, in 0.1.0;
  - of Lemma 6 and Theorems 7–9, in 0.2.0.
  
  Their fixes are applied. The sector form of Lemma 2 (0.3.0) and the
  arborescence section (Lemma A, Proposition B, Theorem M; 0.4.0) have not
  been reviewed.
- **Prior art.**
  - The abelian case is BKR's Proposition 6.19.
  - The `SO(3)` classification and the conjecture itself are Gaetz's (2016).
  - No later answer to Gaetz's Question 2 was found. This is not a novelty
    determination.
  
  See `review/PRIOR_ART.md`.
- Structure beyond orders. For example, `K ≅ (ℤ/4)²` for dihedral groups with
  `m` even is computed for `m ≤ 30` only.

## Reproduction

Needs GAP 4 with SmallGrp and CTblLib, Python 3 and mpmath.

```text
python -B discoveries/combinatorics/mckay-critical-group-minimal/verification/reference/check_mckay_minimal.py
```

The large scans are listed in `verification/reference/README.md`.
