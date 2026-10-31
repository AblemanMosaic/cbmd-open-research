# Written argument

## Setting

`G` is a finite group and `γ : G → SL_n(ℂ)` a faithful representation with
character `χ = χ_γ`. Let `χ_0 = 1, χ_1, …, χ_ℓ` be the irreducible
characters, with degrees `δ_i`.

- **McKay matrix.** `M_{ij}` is the multiplicity of `χ_j` in `γ ⊗ χ_i`.
- **Critical group.** The extended McKay–Cartan matrix is `C̃ = nI − M`, with
  indices `0, …, ℓ`. `C` is `C̃` with the row and column of `χ_0` deleted.
  The critical group is `K(γ) = coker C`. BKR use `coker Cᵗ`, which is the
  same abelian group.

Three known facts are used throughout.

- **(F1)** BKR, Theorem 1.3: there is a surjection `K(γ) ↠ (G^{ab})^`.
- **(F2)** BKR, Theorem 1.4: if `n = 2`, this surjection is an isomorphism.
- **(F3)** Gaetz, *Critical groups of group representations*, Theorem 3(i):
  `|G| · |K(γ)| = Π_{c ≠ 1} (n − χ(c))`. The product runs over the
  nontrivial conjugacy classes, one factor per class.

**Question (BKR, Question 6.11).** For which faithful `γ : G ↪ SL_n(ℂ)` is
the surjection (F1) an isomorphism? We call such `γ` *minimal*.

**Abelian case.** For abelian `G`, `γ` is a multiset `S` of characters, that
is, of elements of the dual group `Ĝ`. Then `det γ = 1` says `Σ S = 0`,
faithfulness says `S` generates `Ĝ`, and `K(γ)` is the Jacobian of the Cayley
digraph `Cay(Ĝ, S)`. The minimal cases are exactly `Ĝ` cyclic with
`S = {a, −a}` plus zeros. This is proved in `CBMD-COMB-CAYLEY-JAC-001`, and
may already be BKR's Proposition 6.19; see `review/PRIOR_ART.md`.

## Lemma 1 (reductions)

**(a)** `K(γ ⊕ 1) = K(γ)`. Adding a trivial summand replaces `n` by `n + 1`
and `M` by `M + I`, so `C̃` does not change. Faithfulness and `det = 1` are
preserved.

**(b)** `γ` is minimal ⟺ `|K(γ)| = |G^{ab}|` ⟺
`Π_{c≠1} (n − χ(c)) = |G| · |G^{ab}|`. The first equivalence holds because a
surjection between finite groups of equal order is an isomorphism (F1). The
second is (F3).

By (a), we may assume `γ` has **no trivial constituent**. Then `n ≥ 2` when
`G ≠ 1`, because a 1-dimensional representation with trivial determinant is
trivial. Every faithful `γ` with `n = 2` is minimal (F2).

## Lemma 2 (adding real summands strictly enlarges `K`)

Let:

- `γ_1` be faithful with `det γ_1 = 1`;
- `γ_2` have `det γ_2 = 1`, and not be a multiple of the trivial
  representation;
- both characters `χ_1, χ_2` be real-valued.

Then `|K(γ_1 ⊕ γ_2)| > |K(γ_1)| ≥ |G^{ab}|`, so `γ_1 ⊕ γ_2` is not minimal.

*Proof.* Let `g ≠ 1`, and let `ε_1, …, ε_{n_1}` be the eigenvalues of the
unitary matrix `γ_1(g)`. Since `χ_1(g)` is real,
`n_1 − χ_1(g) = Σ_j (1 − Re ε_j)`. Every term is `≥ 0`, and the sum is `> 0`
because `γ_1(g) ≠ I`. In the same way `n_2 − χ_2(g) ≥ 0`, with strict
inequality for every `g ∉ ker γ_2 ≠ G`. So each factor of the product (F3) for
`γ_1 ⊕ γ_2` is at least the corresponding factor for `γ_1`, and at least one
is strictly larger. The second inequality is (F1). ∎

Lemma 2 needs the characters to be real. For complex values `|z + w|` can be
smaller than `|z|` even when `Re w ≥ 0`. We do not know whether the lemma
holds without the reality assumption.

## Proposition 3 (from `SU(2)` to `SO(3)`)

Let `π : SU(2) → SO(3)` be the double cover. Let `G ⊂ SO(3)` be finite with
`γ` its inclusion, let `G̃ = π^{−1}(G) ⊂ SU(2)`, and let `ρ` be the natural
representation of `G̃`. Let `u` be the number of conjugacy classes `c̃` of
`G̃` with `−c̃ = c̃`. Then

    |K(γ)| = 2^{u−1} · |G̃^{ab}|.

*Proof.*

1. **Character identity.** `γ ∘ π ≅ Sym²ρ` (the adjoint representation of
   `SU(2)`). For `det ρ = 1`,
   `χ_{Sym²ρ}(x) = (χ_ρ(x)² + χ_ρ(x²))/2 = χ_ρ(x)² − 1`.
   Since `−1` is central and `ρ(−x) = −ρ(x)`, for every `x ∈ G̃`
   
       3 − χ_γ(π x) = 4 − χ_ρ(x)² = (2 − χ_ρ(x)) (2 − χ_ρ(−x)).        (∗)

2. **Classes.** For a class `c` of `G`, `π^{−1}(c)` is a single `G̃`-class
   `c̃ = −c̃` (*non-split*), or two classes `c̃ ≠ −c̃` (*split*). This is because
   `π(y) ~ π(x)` forces `y ~ ±x`. The identity class splits into `{1}` and
   `{−1}`. On a non-split class `χ_ρ(x) = χ_ρ(−x) = −χ_ρ(x)`, so `χ_ρ = 0`.
   There the `G`-factor `3 − χ_γ(c)` is `4`, while the single `G̃`-factor is
   `2`.

3. **Comparing the products.** By (∗), each split class `c ≠ 1` contributes
   the same amount to `Π_{c≠1}(3 − χ_γ(c))` as its two lifts contribute to
   `Π_{c̃≠1}(2 − χ_ρ(c̃))`. The class `{−1}` contributes `2 − (−2) = 4`. So
   
       Π_{c̃ ≠ 1} (2 − χ_ρ(c̃)) = 4 · 2^{−u} · Π_{c ≠ 1} (3 − χ_γ(c)).

4. **Conclusion.** By (F3) the left side is `|G̃| |K(ρ)|`, which equals
   `2|G| · |G̃^{ab}|` by (F2). The right side is `4 · 2^{−u} · |G| |K(γ)|`.
   Hence `|K(γ)| = 2^{u−1} |G̃^{ab}|`. ∎

**Corollary.** Since `G = G̃/⟨−1⟩`, we have `|G^{ab}| = |G̃^{ab}|` if
`−1 ∈ [G̃, G̃]`, and `|G̃^{ab}|/2` otherwise. Therefore `γ` is minimal if and
only if

- `u = 0` and `−1 ∉ [G̃, G̃]`, or
- `u = 1` and `−1 ∈ [G̃, G̃]`.

## Theorem 4 (orthogonal 3-dimensional representations)

Let `G ⊂ SO(3)` be a finite nontrivial subgroup, with `γ` its inclusion.
Then `γ` is minimal if and only if `G` is one of:

- cyclic;
- dihedral of order `2m` with `m` odd;
- `A_4`;
- `A_5`.

For the non-minimal groups:

- for dihedral `G` of order `2m` with `m` even (including `V_4`, `m = 2`),
  `|K(γ)| = 16` while `|G^{ab}| = 4`;
- for `S_4`, `|K(γ)| = 4` while `|G^{ab}| = 2`.

*Proof.* By the classification of finite rotation groups, `G` is cyclic,
dihedral, `A_4`, `S_4` or `A_5`. For each family we compute `u` and decide
whether `−1 ∈ [G̃, G̃]`, then apply the Corollary.

- **Cyclic `C_m`.** `G̃ = C_{2m}` is abelian. All classes are singletons, so
  `u = 0`, and `[G̃, G̃] = 1`. Minimal. Here `γ = 1 ⊕ λ ⊕ λ̄` reduces to
  `n = 2`.
- **Dihedral of order `2m`.** `G̃ = Dic_m = ⟨a, x | a^{2m}, x² = a^m,
  x a x^{−1} = a^{−1}⟩`, with `−1 = a^m`.
  - `[G̃, G̃] = ⟨a²⟩`, which contains `a^m` iff `m` is even.
  - Rotation-type classes are `{a^k, a^{−k}}`. Such a class equals its
    negative iff `a^{k+m} = a^{−k}`, iff `m` is even and `k ≡ m/2 (mod m)`.
    That gives one class when `m` is even, none when `m` is odd.
  - The class of `x a^j` is `{x a^l : l ≡ j (mod 2)}`, and
    `−x a^j = x a^{j+m}`. So the two reflection-type classes are each
    non-split iff `m` is even.
  - Hence `m` odd gives `u = 0` with `−1 ∉ [G̃, G̃]`: minimal. `m` even gives
    `u = 3` with `−1 ∈ [G̃, G̃]`: `|K(γ)| = 4 · |G̃^{ab}| = 16`, since
    `G̃^{ab} = (ℤ/2)²`.
- **`A_4`.** `G̃ = SL(2,3)`, with `[G̃, G̃] = Q_8 ∋ −1`. The six elements of
  order 4 form one class, which equals its negative. The two classes of
  order 3 are sent by `x ↦ −x` to the classes of order 6. So `u = 1`:
  minimal, with `|K| = |G̃^{ab}| = 3`.
- **`S_4`.** `G̃ = 2O`, with `[G̃, G̃] = 2T ∋ −1`. The classes with
  `χ_ρ = 0` are the six elements `±i, ±j, ±k` and the twelve elements of
  order 4 over the half-turns about edge axes. Each equals its negative. The
  two classes of order 8 have `χ_ρ = ±√2` and are swapped. So `u = 2`, and
  `|K(γ)| = 2 · |G̃^{ab}| = 4`.
- **`A_5`.** `G̃ = 2I` is perfect. The thirty elements of order 4 form one
  class equal to its negative. Every other class has `χ_ρ ≠ 0`. So `u = 1`:
  minimal, with `|K| = 1`. ∎

`so3.g` checks every entry of this proof: `u`, `[G̃, G̃]`, `|K(ρ)|`, `|K(γ)|`,
the formula of Proposition 3, Gaetz versus the Smith normal form, and the
isomorphism type. It covers the cyclic and dihedral groups with `m ≤ 30`,
together with `A_4`, `S_4` and `A_5`. The Smith normal forms also show
`K(γ) ≅ (ℤ/4)²` for dihedral groups with `m` even, and `K(γ) ≅ ℤ/4` for
`S_4`. These structural statements are computational for `m ≤ 30` and are
not proved here.

**Real-valued characters in dimension 3.** Suppose `n = 3`, `χ` is
real-valued, and `γ` has no trivial constituent. Look at the constituents of
Frobenius–Schur indicator `−1` (quaternionic type).

- Such a constituent `ψ` has even dimension, so it would be 2-dimensional.
  Its complement would be a real 1-dimensional character `λ`.
- `ψ` preserves a symplectic form, so `det ψ = 1`, and therefore
  `λ = det γ = 1`. This contradicts the assumption of no trivial
  constituent.

So no constituent is quaternionic. The remaining constituents are of real
type, or occur in complex-conjugate pairs (because `χ` is real-valued). Each
of these is realisable over `ℝ`, so `γ` is realisable over `ℝ`. It is then
conjugate into `O(3)`, and into `SO(3)` since `det γ = 1`.

Theorem 4 therefore classifies the minimal `γ` with `n = 3` and real-valued
character: the dihedral groups of order `2m` with `m` odd, `A_4` and `A_5`.

## Proposition 5 (primitive subgroups of `SL_3(ℂ)`)

Blichfeldt's primitive finite subgroups of `SL_3(ℂ)` (types E–L) are:

- the Hessian groups of orders 108, 216 and 648;
- `A_5`, `A_5 × C_3`;
- `PSL(2,7)`, `PSL(2,7) × C_3`;
- the Valentiner group `3.A_6`.

For every faithful 3-dimensional irreducible character with trivial
determinant of each of these, the critical group was computed exactly by
`prim.g` (Gaetz's formula and Smith normal form agree):

| group | `|G|` | `G^{ab}` | `K(γ)` |
|---|---:|---|---|
| `A_5` | 60 | 1 | 0 |
| `PSL(2,7)` | 168 | 1 | `ℤ/2` |
| Hessian | 108 | `ℤ/4` | `ℤ/39 ⊕ ℤ/1092` |
| Hessian | 216 | `(ℤ/2)²` | `ℤ/13 ⊕ ℤ/26 ⊕ ℤ/546` |
| Hessian | 648 | `ℤ/3` | `ℤ/3 ⊕ ℤ/171 ⊕ ℤ/575757` |
| `A_5 × C_3` | 180 | `ℤ/3` | `ℤ/18 ⊕ ℤ/3906` |
| `PSL(2,7) × C_3` | 504 | `ℤ/3` | `ℤ/9 ⊕ ℤ/70434` |
| `3.A_6` | 1080 | 1 | `ℤ/6 ⊕ ℤ/16926` |

Only `A_5` is minimal. This is an exact computation from the character
tables of GAP's libraries, not a hand proof. For `PSL(2,7)` it is also a
two-line hand check by (F3). The classes give factors `4`, `3`, `2` and
`|3 − α|² = 14` with `α = (−1 + √−7)/2`. So `|K| = 4·3·2·14/168 = 2`.

## Conjecture 6

Let `γ : G ↪ SL_n(ℂ)` be faithful with no trivial constituent. Then
`K(γ) ≅ (G^{ab})^` if and only if either:

- `n = 2`; or
- `n = 3`, `χ_γ` is real-valued, and `G` is dihedral of order `2m` with `m`
  odd, or `A_4`, or `A_5`.

Equivalently: `γ(G)` is a finite subgroup of `SL_2(ℂ)`, or one of the
rotation groups `D_{2m}` (`m` odd), `A_4`, `A_5` acting on `ℂ³` without a
fixed vector.

**What is proved.**

| case | status |
|---|---|
| `G` abelian | theorem (`CBMD-COMB-CAYLEY-JAC-001`; possibly BKR Prop. 6.19) |
| `n = 2` | theorem (BKR) |
| `n = 3`, `χ` real-valued | theorem (Theorem 4) |
| `n = 3`, `γ` primitive | exact computation (Proposition 5) |
| `n = 3`, monomial or reducible, `χ` not real | evidence only |
| `n ≥ 4` | evidence only; Lemma 2 excludes real `γ` with a faithful real summand of determinant 1 whose complement also has determinant 1 |

**Evidence.** `evidence/mckay_scans.json` records exhaustive scans over
GAP's SmallGroups library:

- every faithful `γ` into `SL_n` with no trivial constituent;
- for every group of order `≤ 40`, `n ≤ 5`;
- for every non-abelian group of order `≤ 150` except order 128, `n ≤ 6`.

It also records ATLAS character tables of 47 groups with `n ≤ 8`. Of these, 27
have at least one faithful representation of that size into `SL_n`, among
them `A_5`, `2.A_5`, `S_5`, `L_2(7)`, the covers of `A_6` and `A_7`, `U_3(3)`
and `U_4(2)`. In every case the minimal representations are exactly
the predicted ones, and no case violates (F1).

## Remarks

- **What `n = 2, 3` share.** In every minimal case each element of `G` has at
  most two eigenvalues different from 1. In the language of invariant theory,
  `γ(G)` consists of bireflections. For `n = 3` the reason the factorisation
  works is (∗): `4 − ρ²` factors in the representation ring of `G̃`. We do not
  know a proof that minimality forces bireflections. Even with bireflections,
  minimality can fail (dihedral groups with `m` even, and `S_4`).
- **The `n ≥ 4` difficulty.** The abelian proof combined a `p`-adic count
  over Galois orbits of characters (the analogue of the classes here) with an
  AM–GM bound. For non-abelian `G`, (F3) has one factor per class but divides
  by `|G|`, which can be much larger than the number of classes. So the
  `p`-adic count no longer closes on its own.
- **Restriction and induction.** Agarwal and Gaetz (arXiv:1710.08253, Section 3)
  construct restriction maps `K(γ) → K(γ|_H)`. These need not be surjective;
  their Example 3.3 is the dihedral group of order 10 restricted to `C_5`.
  The arguments here do not use these maps.
