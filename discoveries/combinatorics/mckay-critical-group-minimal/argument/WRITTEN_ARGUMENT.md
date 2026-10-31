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

**Gaetz's Question 2.** In his 2016 Minnesota honors thesis (*Critical
groups of McKay–Cartan matrices*), C. Gaetz lists the minimal pairs he knows
(Theorem 8):

- finite subgroups of `SL_2(ℂ)`;
- the cyclic rotation groups;
- the dihedral rotation groups `I_2(n)` with `n` odd;
- `A_4` and `A_5` in `SO(3)`.

He proves this list is complete among subgroups of `SO(3)`, by explicit
computation case by case. He then asks (Question 2) whether these are the
only minimal pairs, up to trivial summands. Theorem 9 below answers his
question affirmatively for `n = 3`. Conjecture 10 is his question for
`n ≥ 4`.

**Abelian case.** For abelian `G`, `γ` is a multiset `S` of characters, that
is, of elements of the dual group `Ĝ`. Then `det γ = 1` says `Σ S = 0`,
faithfulness says `S` generates `Ĝ`, and `K(γ)` is the Jacobian of the Cayley
digraph `Cay(Ĝ, S)`. The minimal cases are exactly `Ĝ` cyclic with
`S = {a, −a}` plus zeros. This is BKR's Proposition 6.19 (proof sketch due to S. Koplewitz).
An independent proof with quantitative bounds is in `CBMD-COMB-CAYLEY-JAC-001`.

## Lemma 1 (reductions)

**(a)** (BKR, Proposition 6.12.) `K(γ ⊕ 1) = K(γ)`. Adding a trivial summand replaces `n` by `n + 1`
and `M` by `M + I`, so `C̃` does not change. Faithfulness and `det = 1` are
preserved.

**(b)** (Gaetz, Corollary 4.) `γ` is minimal ⟺ `|K(γ)| = |G^{ab}|` ⟺
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

*Prior art.* The classification in Theorem 4 is Gaetz's Theorem 8(ii),
including the structures `(ℤ/4)²` and `ℤ/4` in the non-minimal cases. Gaetz
proves it by computing representation rings case by case. The proof below
derives it uniformly from Proposition 3.

Let `G ⊂ SO(3)` be a finite nontrivial subgroup, with `γ` its inclusion.
Then `γ` is minimal if and only if `G` is one of:

- cyclic;
- dihedral of order `2m` with `m ≥ 3` odd;
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

`K(γ)` depends only on the subgroup `γ(G)`. Relabelling `G` by an
isomorphism permutes irreducible characters compatibly (BKR,
Proposition 6.12). Also, `π^{−1}(γ(G))` is determined by the isomorphism
type of `γ(G)` as a rotation group. So Theorem 4 classifies the minimal `γ`
with `n = 3`, real-valued character and no trivial constituent: the dihedral
groups of order `2m` with `m ≥ 3` odd, `A_4` and `A_5`. The cyclic rotation
groups have a trivial constituent, and `m = 1` would be `C_2`, which has no
such representation.

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

## Lemma 6 (abelian product bound)

Let `A` be a finite subgroup of the diagonal torus `T ⊂ SL_3(ℂ)`. Write
`λ_1, λ_2, λ_3` for the coordinate characters, so `λ_1 λ_2 λ_3 = 1`. Let
`A_j = {a ∈ A : λ_j(a) = 1}`. Then each `A_j` is cyclic, of order `m_j` say,
and

    Π_{a ∈ A∖1} |3 − χ(a)| ≥ (m_1 m_2 m_3)² · (3/2)^{|A| + 2 − m_1 − m_2 − m_3}.

*Proof.*

1. **The subgroups `A_j`.** If two coordinates of `a` equal 1, so does the
   third, so `a = 1`. Hence the `A_j` meet pairwise trivially. On `A_1` the
   character `λ_2` is injective, and `χ(a) = 1 + λ_2(a) + λ_2(a)^{−1}`. So
   `A_1` is cyclic and `Π_{a ∈ A_1∖1} |3 − χ(a)| = Π |1 − λ_2(a)|² = m_1²`.
   The same holds for `A_2` and `A_3`.
2. **The remaining elements.** The rest,
   `B = A ∖ (A_1 ∪ A_2 ∪ A_3)`, has `|A| + 2 − Σ m_j` elements and is a union
   of Galois orbits `{a^k : k ∈ (ℤ/d)^×}` (`d` the order of `a`). The product
   over one orbit is `N_{ℚ(ζ_d)/ℚ}(Σ_j (1 − λ_j(a)))`, with all three
   `λ_j(a) ≠ 1`. By Lemma 4 of `CBMD-COMB-CAYLEY-JAC-001` (applied to `Â`,
   the multiset `{λ_1, λ_2, λ_3}` and evaluation at `a`), this product is at
   least `(3/2)^{φ(d)}`. ∎

## Theorem 7 (monomial case: Blichfeldt types C and D)

Let `G ⊂ SL_3(ℂ)` be finite and monomial, with transitive permutation image
`H ∈ {C_3, S_3}`. Then the inclusion is minimal if and only if, up to
conjugacy, `G` is one of:

- `C_3` acting by permutation matrices (this has a trivial constituent, so it
  reduces to `n = 2`);
- `S_3` acting by signed permutation matrices (this is `sgn ⊕ std`, the
  dihedral group of order 6 in `SO(3)`);
- `A_4 = V_4 ⋊ C_3`: the diagonal sign matrices of determinant 1, extended
  by the cyclic permutation matrices (the rotation group of the
  tetrahedron).

*Normal form.* `A = G ∩ T` is normal, and `H` permutes coordinates. Let
`s = D P_σ` be a lift of a 3-cycle, with `det D = 1`. Conjugating by a
diagonal matrix `c ∈ GL_3` replaces `D` by `c D σ(c)^{−1}`. The equations
`c_{σ(i)}/c_i = D_{ii}` are solvable because `Π D_{ii} = 1`. So we may take
`s = P_σ`. All three `A_j` are then conjugate under `P_σ` and have a common
order `m`. Since `A ⊇ A_1 A_2 ≅ C_m²`, `m²` divides `|A|`. Let `f` be the
number of scalar matrices in `A`, so `f ∈ {1, 3}`.

**Type C (`H = C_3`).** `G' = G = A ⋊ ⟨P_σ⟩`.

- **Outside `A`.** Every element outside `A` has zero diagonal, so `χ = 0`
  and its factor in (F3) is 3. Each nontrivial coset contains
  `|A/(1−σ)A| = |A^σ| = f` classes, so there are `2f` such classes in all.
- **Abelianisation.** `[G, G] = (1−σ)A`, so `|G^{ab}| = 3f`.
- **Inside `A`.** The classes are the `σ`-orbits on `A ∖ 1`.

Let `X` be the product of `3 − χ` over the free orbits. Then
`Π_{a ≠ 1} (3 − χ(a)) = X³ · 27^{[f=3]}`, and
`P = Π_{c≠1} (3 − χ(c)) = 3^{2f} · X · 27^{[f=3]}`. Minimality is
`P = 9f|A|`.

- **`f = 1`.** Minimality reads `X = |A|`, that is,
  `Π_{a≠1} |3 − χ(a)| = |A|³`. By Lemma 6 this forces
  `m^6 (3/2)^{|A|−3m+2} ≤ |A|³`. Writing `|A| = k m²`, this is impossible for
  `m ≥ 3`. It forces `|A| ≤ 12` for `m = 2`, and `|A| ≤ 24` for `m = 1`.
- **`f = 3`.** Minimality reads `Π_{a≠1} |3 − χ(a)| = |A|³ / 3^{15}`.
  - If `|A| ≤ 3^5`, the right side is at most 1. The left side is at least
    `m^6 (3/2)^{|A|−3m+2} > 1`, because `|A| ≥ max(3, m²)`.
  - If `|A| > 3^5`, the left side is at least `(3/2)^{|A|/2}`, which exceeds
    `|A|³`.

**Type D (`H = S_3`).** Let `G'` be the preimage of `A_3`; it is of type C.
Let `e = |A^τ|` for the transposition `τ = (1 2)`.

- **Classes.**
  - The classes in `G' ∖ A` fuse in pairs: there are `f` of them, each with
    factor 3.
  - The transposition cosets are all conjugate. They contain `e` classes,
    with `χ = w` a root of unity, so each factor has `|3 − w| ≥ 2`.
  - The classes in `A ∖ 1` are the `S_3`-orbits.
- **Products.** Let `Y` be the product over the `S_3`-orbits, and `X` the
  product over the `σ`-orbits. An `S_3`-orbit is one `σ`-orbit (fixed by
  `τ`) or two. A `τ`-fixed free `σ`-orbit contains exactly one element
  `diag(x, x, x^{−2})` of `A^τ`. Hence `Y² = X · Q · F`, where
  - `Q = Π_{a ∈ A^τ∖scalars} |3 − 2x − x^{−2}|`, and
    `3 − 2x − x^{−2} = −(x−1)²(2x+1)/x²`, so `Q ≥ e²/9^{[f=3]}`;
  - `F = 27^{[f=3]}`.
- **Abelianisation.** `[G, G] ∩ A ⊇ (1−σ)A + (1−τ)A`, so
  `|G^{ab}| ≤ 2 min(e, f)`.
- **The constraint.** Minimality gives
  `Y · 3^f · 2^e ≤ |P| = 6|A| · |G^{ab}| ≤ 12|A| min(e, f)`.
- **The cyclic subgroups.** `A^τ ⊇ {diag(x, x, x^{−2}) : x ∈ μ_m}`, so
  `e ≥ m`.

Combining these with Lemma 6:

- **`f = 1`.** We get `m · e · 2^e · (3/2)^{(|A|−3m+2)/6} ≤ 4|A|`. This is
  impossible for `m ≥ 3`. It forces `|A| ≤ 36` for `m = 2`, and `|A| ≤ 75`
  for `m = 1`.
- **`f = 3`.** Here `e ≥ 3`, and we get
  `93 · m · (3/2)^{(|A|−3m+2)/6} < |A|`, which never holds.

**Finite check.** `monomial_enum.py` enumerates every group of type C or D
in normal form with `|A| ≤ 76`:

- every `A` that is `C_3`- or `S_3`-stable;
- for type D, every `t = D_d P_τ` modulo `A`.

The diagonal entries of `t` lie in `μ_{2|A|}`. This follows from
`t² ∈ A` and `t P_σ t^{−1} P_σ ∈ A`.

For each group the enumeration computes, exactly:

- the classes;
- `|G^{ab}|`;
- `P` (numerically, with rounding error below `10^{−40}`).

Its counts are 47 groups of type C and 23 of type D. The only minimal ones are
the three listed. GAP recomputed `|G|`, `P` and `|G^{ab}|` from explicit
matrices for every enumerated group of order `≤ 60` (recorded evidence; a run to order `≤ 220` is in progress). ∎

## Theorem 8 (reducible case: Blichfeldt type B)

Let `ρ : G ↪ GL_2(ℂ)` be faithful and irreducible, and
`γ = det ρ^{−1} ⊕ ρ`. If `γ` has no trivial constituent (that is,
`G ⊄ SL_2`), then `γ` is minimal if and only if `G` is dihedral of order `2k`
with `k` odd, acting as `sgn ⊕` (reflection representation), i.e. the
dihedral rotation groups of Theorem 4.

*Proof.* Let `Z` be the centre of `G` (scalar matrices, cyclic of order `z`)
and `Ḡ = G/Z ∈ {D_{2k}, A_4, S_4, A_5}`.

- **Central classes.** For `ζ ∈ μ_z ∖ 1`, `γ(ζ) = diag(ζ^{−2}, ζ, ζ)`. Its
  factor is `3 − 2ζ − ζ^{−2} = −(ζ − 1)²(2ζ + 1)/ζ²`. The product over
  `Z ∖ 1` is `C_z = z² |1 − (−2)^z| / 3`.
- **Non-central classes.** Their factors group into Galois orbits, and each
  orbit gives a positive integer. So `P ≥ C_z`.
- **Abelianisation.** `|G| |G^{ab}| ≤ z² |Ḡ| |Ḡ^{ab}|`.

**Exceptional `Ḡ`.**

- **Bound on `z`.** `|1 − (−2)^z| ≤ 3 |Ḡ| |Ḡ^{ab}|` gives `z ≤ 6` for
  `A_4` and `z ≤ 7` for `S_4` and `A_5`.
- **`z` is even.** `[G, G] ⊂ SL_2` maps onto `[Ḡ, Ḡ]`, so `G` contains
  `Q_8`, `2T` or `2I` respectively. In particular `−1 ∈ G`.
- **The groups.** It follows that `G` is one of:
  - `⟨μ_z, Q_8, ζ w⟩` with `ζ³ ∈ μ_z` (`A_4`);
  - `⟨μ_z, 2T, ζ o⟩` with `ζ² ∈ μ_z` (`S_4`);
  - `μ_z · 2I` (`A_5`);
  
  each with `z ∈ {2, 4, 6}`.
- **Check.** `typeB_exceptional.g` computes all of them. None is minimal
  unless `G ⊂ SL_2`.

**Dihedral `Ḡ`.** The preimage `C̃` of the rotation subgroup is abelian of
index 2, and diagonal in a suitable basis. Elements outside `C̃` swap the two
eigenlines. Write `c = |C̃|`.

- **Classes in `C̃`.** The classes are the central elements together with
  swap-pairs. So their contribution to `P` is
  `sqrt(C_z · Π_{a ∈ C̃∖1} |3 − χ(a)|)`.
- **Abelianisation.** `[G, G] ⊇ (1 − swap) C̃`, so `|G^{ab}| ≤ 2z`.
- **The constraint.** Lemma 6 applies to the coordinates
  `(det^{−1}, α, β)`, with `A_α, A_β` of order `m` and
  `A_ν = C̃ ∩ SL_2` of order `m'`. Minimality gives
  
      |1 − (−2)^z| · m⁴ m'² · (3/2)^{c − 2m − m' + 2} ≤ 48 c².

**Case `C̃ ⊄ SL_2`.** Then `m' ≤ c/2`, and with `m² | c`, `m m' | c`,
`z | c`, the inequality forces `c ≤ 23`, so `|G| ≤ 46`.

**Case `C̃ ⊂ SL_2`.** Then `C̃ = ⟨diag(η, η^{−1})⟩` is cyclic of order `c`.
`det ρ` factors through `G/C̃`, and is not trivial, so `det r = −1` and
`r² = 1`. Then:

- `G` is dihedral of order `2c`, acting as `sgn ⊕` reflection;
- the classes give `P = 4c` for `c` odd, and `P = 32c` for `c` even;
- so `γ` is minimal iff `c` is odd. This agrees with Theorem 4.

**Finite check.** Every group of order `≤ 150` is covered by the exhaustive
`n = 3` scan of SmallGroups, which finds no other minimal case. ∎

## Theorem 9 (the case `n = 3`)

Let `γ : G ↪ SL_3(ℂ)` be faithful without trivial constituent. Then `γ` is
minimal if and only if `χ_γ` is real-valued and `G` is dihedral of order `2m`
with `m` odd, `A_4` or `A_5`.

*Proof.* By Blichfeldt's classification, the inclusion `G ⊂ SL_3(ℂ)` falls
into exactly one of these cases:

- abelian (type A): `CBMD-COMB-CAYLEY-JAC-001`, no minimal case;
- reducible `1 + 2` (type B): Theorem 8;
- irreducible imprimitive, hence monomial with transitive permutation image
  (types C and D): Theorem 7;
- primitive (types E–L): Proposition 5.

In every case the minimal ones are those listed. ∎

Theorems 7, 8 and 9 are computer-assisted. The analytic bounds reduce each
case to finitely many groups, and exact computation settles those groups.

## Conjecture 10 (`n ≥ 4`; Gaetz's Question 2)

Let `γ : G ↪ SL_n(ℂ)` be faithful with no trivial constituent, and `n ≥ 4`.
Then `K(γ) ≇ (G^{ab})^`.

Together with BKR (`n = 2`) and Theorem 9 (`n = 3`), this would answer BKR's
Question 6.11 completely. `γ` would be minimal exactly when `γ(G)` is a
finite subgroup of `SL_2(ℂ)` (plus trivial summands), or one of the rotation
groups `D_{2m}` (`m ≥ 3` odd), `A_4`, `A_5` acting on `ℂ³` without a fixed
vector.

**What is proved.**

| case | status |
|---|---|
| `G` abelian | theorem (BKR Prop. 6.19; independent proof in `CBMD-COMB-CAYLEY-JAC-001`) |
| `n = 2` | theorem (BKR) |
| `n = 3`, `χ` real-valued | theorem (Gaetz, Theorem 8(ii); uniform proof in Theorem 4) |
| `n = 3` | theorem, computer-assisted (Theorem 9) |
| `n ≥ 4` | conjecture; see the evidence below. Lemma 2 excludes a real `γ` that has a faithful real summand of determinant 1 whose complement also has determinant 1. |

**Evidence.** `evidence/mckay_scans.json` records exhaustive scans over
GAP's SmallGroups library. Each covers every faithful `γ` into `SL_n` with
no trivial constituent:

- every group of order `≤ 40`, with `n ≤ 5`;
- every non-abelian group of order `≤ 72`, with `n ≤ 6`;
- every non-abelian group of order `≤ 150`, with `n = 3`.

It also records ATLAS character tables of 47 groups with `n ≤ 8`. Of these, 27
have at least one faithful representation of that size into `SL_n`, among
them `A_5`, `2.A_5`, `S_5`, `L_2(7)`, the covers of `A_6` and `A_7`, `U_3(3)`
and `U_4(2)`.

In every case the minimal representations are exactly the predicted ones.
No case violates (F1), and none has `n ≥ 4`.

## Remarks

- **What `n = 2, 3` share.** In every minimal case each element of `G` has at
  most two eigenvalues different from 1. In the language of invariant theory,
  `γ(G)` consists of bireflections. For `n = 3` the mechanism behind
  Proposition 3 is (∗): `2 + χ_ρ(x) = 2 − χ_ρ(−x)`. This is translation by
  the central element `−1`; it does not come from tensoring with a
  character, since no character with `ε(−1) = −1` exists when
  `−1 ∈ [G̃, G̃]`. We do not
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
