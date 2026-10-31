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

- **(F1)** BKR, Theorem 1.3: for a faithful `γ` **with `det γ = 1`**, that
  is `γ : G ↪ SL_n(ℂ)`, there is a surjection `K(γ) ↠ (G^{ab})^`. The
  determinant hypothesis is stated inline because Lemma A and Theorem M below
  deliberately drop it, and (F1) is false without it: for `G = ℤ/2` and `γ`
  the sign character, `|K(γ)| = 1 < 2 = |G^{ab}|` (gate `M1_HYPOTHESIS`).
- **(F2)** BKR, Theorem 1.4: if `n = 2`, this surjection is an isomorphism.
- **(F3)** Gaetz, *Critical groups of group representations*, Theorem 3(i)
  (the same statement is Theorem 1(i) of his thesis, which is how the
  verification scripts cite it):
  `|G| · |K(γ)| = Π_{c ≠ 1} (n − χ(c))`. The product runs over the
  nontrivial conjugacy classes, one factor per class. Proposition B below
  gives a second, self-contained proof of (F3); it is listed here as a known
  fact because that is how it is used in Theorems 4–9.

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
In that language all degrees are 1, so Lemma A is the ordinary matrix-tree
theorem for the Cayley digraph and Theorem M says that enlarging the
generating multiset `S` by a nonzero element strictly increases
`|Jac(Cay(Ĝ, S))|` — the digraph form of the classical fact that adding an
edge to a connected graph increases its number of spanning trees. For
abelian `G` that case is folklore; the content of Theorem M is that it
survives when the degrees `δ_i` are not all 1.

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

## Lemma A (the arborescence picture)

Everything in this section and the next is *proved by hand*, for arbitrary
`n` and with no determinant, dimension or reality hypothesis.

For a representation `γ` of `G` of degree `n`, write `M = M(γ)`,
`C̃(γ) = nI − M`, and let `Q(γ)` be the McKay quiver: vertices `0, …, ℓ`,
with `M_{ij}` arcs `i → j`. Let `D = diag(δ_0, …, δ_ℓ)` be the diagonal
matrix of degrees, `δ_0 = 1`. An *arborescence rooted at `v`* is a **function**
`T : {0, …, ℓ} ∖ {v} → {0, …, ℓ}` with `M_{i,T(i)} > 0` for every `i`, such
that every vertex has a directed path to `v`. It is a choice of out-*neighbour*,
not of one among the `M_{ij}` parallel arcs: the multiplicity enters through
the weight, which is why `M_{ij}` appears in `w` below and must not be counted
twice. Write `Arb_v` for the set of these and

    A_v(γ) = Σ_{T ∈ Arb_v} Π_{i ≠ v} w(i → T(i)),    w(i → j) := M_{ij} δ_j / δ_i ≥ 0.

Self-loops play no part: `T(i) = i` is excluded, matching `L̃_{ii} = n − M_{ii}`
below, which is the loop-free weighted out-degree. Loops do occur, for instance
`M_{ii} = 1` for `G = S_3` at the standard character.

**Lemma A.** `det C(γ) = A_0(γ)`, for *any* representation `γ`, faithful or
not. In particular `det C(γ) ≥ 0`, as a sum of nonnegative terms. When `γ` is
faithful, `det C(γ) = |K(γ)|`. When it is not, **both sides are 0**: the corank
of `C̃(γ)` is the number of conjugacy classes inside `ker γ`, which is then at
least 2, so every `ℓ × ℓ` minor vanishes; equivalently, the `ker γ`-isotype of
`χ_i` is constant along arcs of `Q(γ)`, so no vertex whose restriction to
`ker γ` is nontrivial can reach `0` and `Arb_0` is empty. Only the inequality
`det C(γ) ≥ 0` is used below.

*Proof.* Evaluating `χ_γ χ_i = Σ_j M_{ij} χ_j` at the identity gives
`Σ_j M_{ij} δ_j = n δ_i`, that is `M δ = n δ` where `δ = (δ_0, …, δ_ℓ)`
(Gaetz, Proposition 4(i); in the language of Browne, Proposition 5.2, the
weight vector of a McKay quiver is its dimension vector). Put

    L̃ := D^{-1} C̃(γ) D,     L̃_{ij} = −M_{ij} δ_j / δ_i  (i ≠ j),   L̃_{ii} = n − M_{ii}.

Its off-diagonal entries are `≤ 0` and, by `M δ = n δ`, its **row** sums
vanish. So `L̃` is the Laplacian of the weighted digraph on `{0, …, ℓ}` with
arc weights `w(i → j)`, and Tutte's weighted matrix-tree theorem for digraphs
gives that the determinant of `L̃` with row and column `v` struck is
`A_v(γ)`. The orientation is load-bearing: vanishing *row* sums are the
convention under which the minor counts arborescences pointing **toward** the
struck vertex, which is what `Arb_v` is. Tutte's theorem is as often quoted for
out-trees, and the two readings genuinely differ — for `G = A_4` with its
3-dimensional irreducible, `δ = (1,1,1,3)` and `det C = 3 = A_0`, while the
same sum over arborescences oriented away from `0` is `1/3`. They agree for
abelian `G`, where `M` is a sum of permutation matrices and both row and
column sums are `n`, which is why small abelian examples hide the issue. Striking the same index from rows and from columns commutes with
conjugating by a diagonal matrix, so that determinant equals
`det(C̃(γ)` with row and column `v` struck`)`; for `v = 0` this is
`det C(γ)`. ∎

The weights are rational, not integral, so this is not an instance of the
integer-outdegree digraph theory recalled in BKR, Remark 2.18: the outdegree
of `i` in `Q(γ)` is `Σ_j M_{ij}`, which equals `n` only in special cases. It
is the *weighted* outdegree `Σ_j M_{ij} δ_j / δ_i` that is `n` at every
vertex.

**Proposition B.** Let `γ` be **faithful**. Then `A_v(γ) = δ_v² · det C(γ)`
for every `v`, and consequently `|G| · det C(γ) = Π_{c ≠ 1}(n − χ_γ(c))`.

(The first identity in fact holds for every representation: if `γ` is not
faithful then `C̃(γ)` has corank `≥ 2`, so every `ℓ × ℓ` minor vanishes and
both sides are 0. Faithfulness is needed for the *argument* below, which uses
corank exactly 1, and for the second identity. This matters because Theorem M
applies the arborescence picture to a `γ_2` that may well be non-faithful.)

*Proof.* By Lemma A's proof, `A_v(γ)` is the `(v,v)` cofactor of `C̃(γ)`.
Faithfulness gives `χ_γ(c) ≠ n` for `c ≠ 1`, so by Gaetz, Proposition 4,
`C̃(γ)` has corank exactly 1; it has right nullvector `δ`, as above, and also left
nullvector `δ`: the `i`-th entry of `Mᵗδ` is
`Σ_j M_{ji} δ_j = ⟨χ_reg χ_γ, χ_i⟩ = n δ_i` (this is the computation in the
proof of Gaetz, Proposition 4(iii); for Hopf algebras the two relations are
Grinberg–Huang–Reiner, Propositions 3.1 and 3.8). For a matrix of corank 1
the adjugate is `κ · x yᵗ` with `x`, `y` spanning the right and left
nullspaces, so the `(v,v)` cofactor is `κ δ_v²`; taking `v = 0` gives
`κ = A_0(γ) = det C(γ)` since `δ_0 = 1`.

For the second claim, the coefficient of `x¹` in `det(xI − C̃(γ))` is
`(−1)^ℓ e_ℓ`, where `e_ℓ` is the elementary symmetric function of the
eigenvalue multiset `{0} ∪ {n − χ_γ(c) : c ≠ 1}` (Gaetz, Proposition 4(ii)),
so `e_ℓ = Π_{c≠1}(n − χ_γ(c))`, the only `ℓ`-subset of the multiset that
avoids the eigenvalue `0`. That same coefficient is `(−1)^ℓ` times the sum of
the principal `ℓ × ℓ` minors of `C̃(γ)`. The two factors `(−1)^ℓ` cancel, so

    Π_{c≠1}(n − χ_γ(c)) = Σ_v (v,v) cofactor of C̃(γ) = Σ_v A_v(γ)
                        = det C(γ) · Σ_v δ_v² = |G| · det C(γ). ∎

Both signs are needed; neither alone. For `G = ℤ/2` and `γ = sgn`,
`C̃ = [[1,−1],[−1,1]]` and `det(xI − C̃) = x² − 2x`, whose `x¹` coefficient is
`−2`, while `Σ_v A_v = 2`. An earlier draft of this proof asserted the
unsigned form of both statements; they are false for odd `ℓ`, and the
conclusion survived only because the error occurred twice with opposite
effect. It was caught in independent review (0.4.2).

So (F3) is recovered, by elementary linear algebra and without Lorenzini's
cokernel theorem; only the identification of the `(v,v)` cofactor with `A_v`
uses the matrix-tree theorem, and the second half of Proposition B — read as
a statement about cofactors — uses none. For a
one-dimensional `χ_v` the identity `A_v = A_0` also has a direct reason:
`χ_i ↦ χ_i ⊗ χ_v` is a quiver automorphism carrying `0` to `v` (Browne,
Lemma 4.1), hence a weight-preserving bijection `Arb_0 → Arb_v`. Dropping
acyclicity from Lemma A gives the upper bound
`det C(γ) ≤ Π_{i ≠ 0}(n − M_{ii})`.

## Theorem M (adding a summand enlarges `K`, unconditionally)

**Theorem M.** Let `γ_1` be a faithful representation of `G` and `γ_2` any
representation of `G`. Then

    |K(γ_1 ⊕ γ_2)| ≥ |K(γ_1)|,

with equality if and only if `γ_2` is a multiple `m · χ_0` of the trivial
representation, `m ≥ 0` included (for `m = 0` there is nothing to prove).

In the form `det C(γ_1 ⊕ γ_2) ≥ det C(γ_1)` the inequality holds for
*arbitrary* `γ_1`, faithful or not, since that is all the expansion below
uses. Faithfulness of `γ_1` enters twice: to read both determinants as orders
of critical groups, and for strictness, where it is genuinely needed — if
`γ_1 ⊕ γ_2` is not faithful then both sides are `0` by Lemma A.

*Proof.* Since `χ_{γ_1⊕γ_2} = χ_{γ_1} + χ_{γ_2}` and `n = n_1 + n_2`, we have
`M(γ_1 ⊕ γ_2) = M(γ_1) + M(γ_2)` and `C̃(γ_1 ⊕ γ_2) = C̃(γ_1) + C̃(γ_2)`; the
same `δ` is a nullvector of both summands, so Lemma A's conjugation serves
both at once and `Q(γ_1 ⊕ γ_2)` is the arc-multiset union
`Q(γ_1) ⊎ Q(γ_2)`. Write `M¹, M²` for the two McKay matrices. By Lemma A,

    |K(γ_1 ⊕ γ_2)| = Σ_T Π_{i≠0} (M¹_{i,T(i)} + M²_{i,T(i)}) δ_{T(i)}/δ_i,

the sum over arborescences of the union quiver rooted at `0`. Expand each
factor and collect by the set `S ⊆ {1, …, ℓ}` of vertices taking their arc
from `γ_1`:

    |K(γ_1 ⊕ γ_2)| = Σ_T Σ_S ( Π_{i∈S} M¹_{i,T(i)} )( Π_{i∉S} M²_{i,T(i)} ) Π_{i≠0} δ_{T(i)}/δ_i,

every term nonnegative. The terms with `S = {1, …, ℓ}` vanish unless `T` is
an arborescence of `Q(γ_1)`, and they sum to `|K(γ_1)|` by Lemma A. Hence
the inequality.

If `γ_2 = m · χ_0` then `M² = mI`, so `C̃(γ_2) = 0` and
`C̃(γ_1 ⊕ γ_2) = C̃(γ_1)`: equality, which is Lemma 1(a).

Otherwise let `χ_j` be a nontrivial irreducible constituent of `γ_2` and let
`u` be the index with `χ_u = χ_j^*`, so `u ≠ 0`. Then

    M²_{u,0} = ⟨χ_{γ_2} χ_u, χ_0⟩ = ⟨χ_{γ_2}, χ_u^*⟩ = ⟨χ_{γ_2}, χ_j⟩ > 0,

so `Q(γ_2)` has an arc `u → 0`. As `γ_1` is faithful, every irreducible
occurs in some tensor power of `γ_1` (Burnside; BKR cite the strengthening
[12, Thm. 9.34]), so `Q(γ_1)` is strongly connected (Browne, Proposition
3.3) and has an arborescence `T` rooted at `0`. Put `T'(i) = T(i)` for
`i ≠ u` and `T'(u) = 0`. Then `T'` is again an arborescence: a cycle of `T'`
cannot contain `0`, which has no out-arc; cannot avoid the arc `u → 0`,
since the remaining arcs are `T`-arcs and `T` is acyclic; and cannot use
`u → 0` either, since that arc *enters* `0`. So the pair
`(T', S = {1, …, ℓ} ∖ {u})` contributes a positive term absent from
`|K(γ_1)|`, and the inequality is strict. ∎

**Corollary M1.** Let `γ : G ↪ SL_n(ℂ)` be faithful and `γ = γ_1 ⊕ γ_2` with
`γ_1` faithful, **`det γ_1 = 1`** (equivalently `det γ_2 = 1`), and `γ_2` not
a multiple of the trivial representation. Then
`|K(γ)| > |K(γ_1)| ≥ |G^{ab}|`, the second inequality by (F1) applied to
`γ_1`, so `γ` is not minimal. Hence in Question 6.11 and Gaetz's Question 2
one may assume that no proper direct summand of `γ` of determinant 1 is
faithful, after deleting trivial summands.

The determinant hypothesis on `γ_1` cannot be dropped: (F1) is a statement
about representations into `SL_n`, and it fails otherwise. The smallest
example is `G = ℤ/2` with `γ_1` the sign character: `C̃ = I − P` for the
transposition `P`, the reduced matrix is `(1)`, and
`|K(γ_1)| = 1 < 2 = |G^{ab}|`. Among all faithful representations of degree
`≤ 3` of the groups of order `≤ 20`, the 591 with `det = 1` all satisfy
`|K| ≥ |G^{ab}|`, as (F1) requires, while 136 of the 10,963 with `det ≠ 1`
have `|K| < |G^{ab}|` (gate `M1_HYPOTHESIS`). Theorem M itself is unaffected — it never
uses (F1). This is also why Theorem 8 is still needed: its
`γ = det ρ^{−1} ⊕ ρ` has `det γ = 1` but `det ρ ≠ 1`, so Corollary M1 does
not apply to it, even though Theorem M does give `|K(γ)| > det C(ρ)`.

**Corollary M2.** Let `G ≠ 1`, so that `ℓ ≥ 1` and the blocks `S = ∅` and
`S = {1, …, ℓ}` are distinct. The terms with `S = ∅` sum to `det C(γ_2)`, so
`|K(γ_1 ⊕ γ_2)| ≥ |K(γ_1)| + det C(γ_2)`; when `γ_2` is also faithful this
reads `|K(γ_1 ⊕ γ_2)| ≥ |K(γ_1)| + |K(γ_2)|`, and the same expansion gives
`|K(γ_1 ⊕ ⋯ ⊕ γ_r)| ≥ Σ_t |K(γ_t)|` for faithful `γ_t`. The hypothesis
`G ≠ 1` is not idle: for `ℓ = 0` the two blocks coincide and the bound would
read `1 ≥ 1 + 1`. The added term is informative only for faithful `γ_2`,
since otherwise `det C(γ_2) = 0` by Lemma A. The bound is tight: for `ℓ = 1`
the expansion has only its two extreme terms, and for `G = ℤ/2` with
`γ_1 = γ_2` the sign character, `1 + 1 = 2`.

Theorem M supersedes the sector form of Lemma 2 below, which proved the
strict inequality only under `det γ_1 = det γ_2 = 1` together with "`χ_1`
real-valued or `1/n_1 + 1/n_2 ≥ 1/2`". The sector lemma is kept because it
is an independent statement about `SU(n)` and makes the per-class factors
geometrically transparent.

## Lemma 2 (adding a summand: the sector form, superseded by Theorem M)

**Sector lemma.** Let `U ∈ SU(n)`. Then `z = n − tr U` is either 0 or
satisfies `|arg z| ≤ π/2 − π/n`. For `n = 2`, `z` is real and `≥ 0`.

*Proof.* Let `e^{iθ_j}` be the eigenvalues of `U`, so `Σ θ_j ∈ 2πℤ`. Put
`φ_j = θ_j − π/n`, reduced to `(−π, π]`. Then `Σ φ_j ≡ π (mod 2π)`, and we
claim

    Σ_j cos φ_j ≤ n cos(π/n).

Let `k` be the number of `j` with `|φ_j| > π/2`.

- **`k = 0`.** `cos` is concave on `[−π/2, π/2]`. Let `S = Σφ_j`; it is an
  odd multiple of `π`, so `|S| ≥ π`. Jensen gives
  `Σ cos φ_j ≤ n cos(S/n) ≤ n cos(π/n)`.
- **`k ≥ 1`.** Each such `j` has `cos φ_j < 0`, so the total is `< n − 1`.
  For `n ≥ 5`, `n − 1 ≤ n cos(π/n)`, since
  `cos x ≥ 1 − x²/2` and `n ≥ π²/2`.
- **Small `n`.**
  - For `n = 2`, `tr U` is real, so the claim is immediate.
  - For `n ∈ {3, 4}` with `k ≥ 2`, the total is `≤ n − 2 < n cos(π/n)`.
  - For `n ∈ {3, 4}` with `k = 1`, apply Jensen to the other `n − 1` terms,
    whose sum is `S − φ`, `|φ| ∈ (π/2, π]`. The total is at most
    `(n−1) cos((π − |φ|)/(n−1)) + cos φ`. This is maximal at
    `|φ| = π/2`, where it equals `2 sin(π/4) ≈ 1.414 < 1.5` (`n = 3`) and
    `3 cos(π/6) ≈ 2.598 < 2.828` (`n = 4`). The cases `|S| ≥ 3π` cannot
    occur, because then the other terms would leave `[−π/2, π/2]`.

So `Re(e^{−iπ/n}(n − tr U)) ≥ 0`. Applying the same to `Ū` gives
`Re(e^{iπ/n}(n − tr U)) ≥ 0`, and the two together are the sector. The bound
is attained by the scalar matrix `ζ_n I`. ∎

Geometrically, `tr SU(n)` lies in the regular `n`-gon with vertices
`n ζ_n^k`, and `π − 2π/n` is that polygon's interior angle.

**Lemma 2.** Let:

- `γ_1` be faithful with `det γ_1 = 1`, of dimension `n_1`;
- `γ_2` have `det γ_2 = 1`, have dimension `n_2`, and not be a multiple of
  the trivial representation.

Suppose that `χ_1` is real-valued, or that `1/n_1 + 1/n_2 ≥ 1/2`. Then
`|K(γ_1 ⊕ γ_2)| > |K(γ_1)| ≥ |G^{ab}|`, so `γ_1 ⊕ γ_2` is not minimal.

*Proof.* For a class `c ≠ 1`, put `a = n_1 − χ_1(c)` and `b = n_2 − χ_2(c)`.

- **`a`.** It is nonzero because `γ_1` is faithful. If `χ_1` is
  real-valued, `a` is real and positive. In any case
  `|arg a| ≤ π/2 − π/n_1`, by the sector lemma.
- **`b`.** It is 0 or satisfies `|arg b| ≤ π/2 − π/n_2`, and `Re b ≥ 0`.
- **The angle.** Under either hypothesis the angle between `a` and `b` is at
  most `π/2`. If `χ_1` is real, `a` points along the positive axis and
  `|arg b| ≤ π/2`. Otherwise,
  `(π/2 − π/n_1) + (π/2 − π/n_2) ≤ π/2`. So `Re(a b̄) ≥ 0`.
- **Each factor.** Hence `|a + b|² ≥ |a|² + |b|²`. So `|a + b| ≥ |a|`, with
  strict inequality whenever `b ≠ 0`, that is, whenever
  `γ_2(c) ≠ I`. Such a class exists because `γ_2` is not trivial.
- **Conclusion.** Multiply over classes, then apply (F3) and (F1). ∎

**When the hypothesis holds.**

- `χ_1` real-valued: any `n_2`. In particular `n_1 = 2`, since a faithful
  `SL_2` representation has real character.
- `n_2 = 2`: any `n_1`.
- `n_1 = 3`: `n_2 ≤ 6`.
- `n_1 = 4`: `n_2 ≤ 4`.
- `n_1 ∈ {5, 6}`: `n_2 ≤ 3`.

**Consequence.** Let `γ` be minimal with no trivial constituent. Then `γ` has
no decomposition `γ_1 ⊕ γ_2` with:

- `γ_1` faithful;
- both summands of determinant 1;
- `γ_2 ≠ 0`;
- the dimension condition above.

This applies, for example, to `γ = (faithful SL_2 rep) ⊕ (anything of
determinant 1)`. It does not touch the case where no faithful summand has
determinant 1. Reducible type B in dimension 3 is such a case, and needs
Theorem 8.

An exhaustive search of the remaining pairs found no violation of
`|K(γ_1 ⊕ γ_2)| > |K(γ_1)|` either. It covered `γ_1` faithful with
determinant 1, `γ_2` with determinant 1 and not trivial, `n_1, n_2 ≤ 4`, and
non-abelian groups of order `≤ 60`: 1,359,437 pairs. So the dimension
condition may be removable.

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
- **Products.** Let `Y` be the product over the `S_3`-orbits. Let `X'` be
  the product over *all* `σ`-orbits on `A ∖ 1`, including the scalar
  singletons, so `X' = X · 27^{[f=3]}` with `X` as in type C. An `S_3`-orbit is one `σ`-orbit (fixed by
  `τ`) or two. A `τ`-fixed free `σ`-orbit contains exactly one element
  `diag(x, x, x^{−2})` of `A^τ`. Hence `Y² = X' · Q · F`, where
  - `Q = Π_{a ∈ A^τ∖scalars} |3 − 2x − x^{−2}|`, and
    `3 − 2x − x^{−2} = −(x−1)²(2x+1)/x²`, so `Q ≥ e²/9^{[f=3]}`;
  - `F = 27^{[f=3]}` comes from the `τ`-fixed scalar singletons.
  
  Check on `A = T[3]`: `Y = 81`, `X' = 9·27`, `Q = 1`, `F = 27`.
  Also `X' ≥ 9^{[f=3]} m² (3/2)^{|B|/3}`, by Lemma 6 and
  `X'³ = Π_{a≠1} · 27^{2[f=3]}`.
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
  `93 · m · (3/2)^{(|A|−3m+2)/6} ≤ |A|`. This never holds:
  - if `|A| ≤ 93`, the left side is at least 93, because the exponent is
    `≥ 0`;
  - beyond that, the exponent is at least `(|A| − 3√|A| + 2)/6`, and the left
    side grows exponentially.

`bounds_check.py` recomputes all four regions by brute force for
`|A| ≤ 4000`. Beyond 4000, each left side exceeds its right side by a factor
that only grows. The exponent is at least `(|A| − 3√|A| + 2)/6`, using
`m ≤ √|A|`.

**Finite check.** `monomial_enum.py` enumerates every group of type C or D
in normal form with `|A| ≤ 76`:

- every `A` that is `C_3`- or `S_3`-stable;
- for type D, every `t = D_d P_τ` modulo `A`.

The diagonal entries of `t` lie in `μ_{2|A|}`. To see this, write
`d = (d_1, d_2, d_3)`. Then:

- `t² = diag(d_1 d_2, d_1 d_2, d_3²) ∈ A`;
- `t P_σ t^{−1} P_σ` is the diagonal matrix of the three cyclic ratios
  `d_i/d_j`, and it also lies in `A ⊂ μ_{|A|}³`.

Hence `d_3 ∈ μ_{2|A|}`, and each `d_i ∈ d_3 · μ_{|A|}`. No further
normalisation of `t` is needed.

For each group the enumeration computes, exactly:

- the classes;
- `|G^{ab}|`;
- `P` (numerically, with rounding error below `10^{−40}`).

Its counts are 47 groups of type C and 23 of type D. The only minimal ones are
the three listed. GAP recomputed `|G|`, `P` and `|G^{ab}|` from explicit
matrices for every enumerated group of order `≤ 220` (59 groups). ∎

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
- **Non-central classes.** Their factors group into Galois orbits of
  classes, and each orbit gives a positive integer. It is a rational integer
  because it is a norm. It is positive because every conjugate
  `3 − χ(c^k)` has positive real part, and the orbit is closed under complex
  conjugation, `c ↦ c^{−1}`. So `P ≥ C_z`.
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

**Dihedral `Ḡ`.** The preimage `C̃` of a cyclic subgroup of index 2 is
abelian of index 2; for `Ḡ = V_4`, any of the three choices works. `C̃` is
diagonal in a suitable basis. It is not scalar, since otherwise `ρ` would be
reducible, so its two eigencharacters are distinct. Elements outside `C̃`
therefore swap the two eigenlines. Write `c = |C̃|`.

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

- `bounds_check.py` searches `c ≤ 4000` and `z ≤ 64`.
- For `z > 64`, `|1 − (−2)^z| > 48 · 4000²` already.
- For `c > 4000`, the exponent is at least `c/2 − 2√c + 2`, because
  `m' ≤ c/2` and `m ≤ √c`.

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
with `m ≥ 3` odd, `A_4` or `A_5`.

*Proof.* `K(γ)` depends only on the subgroup `γ(G)` up to conjugacy
(Lemma 1 and BKR, Proposition 6.12). By Blichfeldt's classification, the
inclusion `γ(G) ⊂ SL_3(ℂ)` falls into one of these cases:

- abelian (type A): `CBMD-COMB-CAYLEY-JAC-001`, no minimal case;
- reducible `1 + 2` (type B): Theorem 8. If the 2-dimensional part is
  itself reducible, `G` is abelian (type A);
- irreducible imprimitive, hence monomial with transitive permutation image
  (types C and D): Theorem 7;
- primitive (types E–L): Proposition 5.

Some reducible monomial groups appear in Theorem 7 as well, for example
`S_3 = sgn ⊕ std`. The overlap is harmless.

For primitive images, Proposition 5 covers every faithful 3-dimensional
irreducible character with trivial determinant of each of the eight abstract
groups. That covers every embedding.

In every case the minimal ones are those listed. The proof depends on the
completeness of Blichfeldt's list, as tabulated by Yau–Yu. ∎

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
| `n ≥ 4` | conjecture; see the evidence below. Lemma 2 excludes every `γ` with a faithful summand of determinant 1 whose complement has determinant 1 and satisfies its dimension condition. |

**Evidence.** `evidence/mckay_scans.json` records exhaustive scans over
GAP's SmallGroups library. Each covers every faithful `γ` into `SL_n` with
no trivial constituent:

- every group of order `≤ 40`, with `n ≤ 5`;
- every non-abelian group of order `≤ 71`, with `n ≤ 6`;
- every non-abelian group of order `≤ 150`, with `n = 3`;
- every non-abelian group of order `72`–`150`, with `n ≤ 4`.

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
