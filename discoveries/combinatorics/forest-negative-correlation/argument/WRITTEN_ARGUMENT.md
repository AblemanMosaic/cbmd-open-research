# Written argument

No conjecture is proved here. This section records the reductions that make
the computations exact and complete for the stated graph classes.

## 1. The quantity checked

Let `G` be a finite multigraph and `λ > 0`. Write `𝓕(G)` for the forests
(acyclic edge sets) and `𝓒(G)` for the connected spanning edge sets of `G`.
Set

- `Z_G(λ) = Σ_{F ∈ 𝓕(G)} λ^{|F|}`, and
- `C_G(λ) = Σ_{A ∈ 𝓒(G)} λ^{|A|}`.

These are the partition functions of the arboreal gas and of the `q → 0`
random-cluster limit.

For distinct edges `e, f` and `X ∈ {Z, C}`, write `X_e`, `X_f`, `X_{ef}` for
the sums restricted to sets containing `e`, `f`, or both. Under the measure
proportional to `λ^{|S|}`, the edges `e` and `f` are negatively correlated iff
`X_e X_f − X X_{ef} ≥ 0`.

**Contraction.** For `e = uv` with `u ≠ v`, the map `S ↦ S − e` is a bijection
between sets in the family that contain `e` and the corresponding sets of the
contracted multigraph `G/e`. For forests, loops of `G/e` are discarded, since
a forest containing `e` never contains an edge parallel to `e`. For connected
sets, loops are kept and may be added freely. Hence `X_e = λ X_{G/e}` and
`X_{ef} = λ² X_{G/e/f}`. If `e` and `f` are parallel copies, `G/e/f` is not
defined. We set `X_{G/e/f} := 0` for forests, since `Z_{ef} = 0`. For
connected sets we set `X_{G/e/f} := C_{(G/e) − f}`, where `f` has become a
loop of `G/e`, since `C_{ef} = λ² C_{(G/e) − f}`. Thus negative correlation is
equivalent to

    P_X(λ) := X_{G/e} X_{G/f} − X_G X_{G/e/f} ≥ 0,

which is an integer polynomial in `λ`. The tools test two things:

- `P_X(1) ≥ 0`, which is the uniform measure (Grimmett–Winkler);
- every coefficient of `P_X` is `≥ 0`. This implies `P_X(λ) ≥ 0` for all
  `λ > 0`, which is the weighted form (Kahn; Grimmett–Winkler (1.6)).

**Computing `X_H`.** `Z_H` is the sum over set partitions of `V(H)` of
`Π τ(H[B]) λ^{|B|−1}`, where `τ` counts spanning trees. Each forest is a
spanning tree on each of its components. The tools evaluate `τ` by
Kirchhoff's theorem, with fraction-free exact determinants. `C_H` follows from
`conn(S) = all(S) − Σ_{B} conn(B)·all(S∖B)`. Here `B` ranges over the proper
subsets of `S` that contain the least vertex of `S`, and
`all(S) = (1 + λ)^{e(S)}`, where `e(S)` counts the edges inside `S`, loops
included. All arithmetic is exact: 64-bit coefficients and 128-bit products.
The largest coefficients that occur, about `2^{36}` for connected sets of
`K_9`, are far from overflow.

## 2. Reduction to 2-connected graphs

Every cycle of `G` lies in a single block (a maximal 2-connected subgraph, or
a bridge). An edge set is a forest iff its restriction to every block is a
forest. A spanning edge set is connected iff its restriction to every block
is connected and spanning on that block. So `X_G = Π_B X_B`, and the
`λ`-weighted measure is the product of the block measures.

- If `e` and `f` lie in different blocks, they are independent and
  `P_X ≡ 0`.
- If both lie in the block `B`, then `P_X(G) = (Π_{B' ≠ B} X_{B'})² · P_X(B)`.

For the connected-subgraph model `G` is assumed connected; otherwise
`C_G ≡ 0` and the measure is undefined. Hence the conjectures hold for all
graphs (all connected graphs, for `C`) on at most `n` vertices iff they hold
for all 2-connected graphs on at most `n` vertices. The square factor has
nonnegative coefficients, so the reduction also holds coefficientwise. A bridge carries only
one edge. The same reduction holds for multigraphs.

## 3. Completeness of the enumeration

The 2-connected graphs come from `geng -C` (nauty 2.8.8, built from the
source shipped in pynauty 2.8.8.1). Its counts 1, 3, 10, 56, 468, 7123,
194066 for 3..9 vertices match OEIS A002218. Within each graph, every
unordered pair of distinct edges is tested, without symmetry reduction. The
multigraph runs use `multig` on the same lists.

## 4. Theorem: the small-`λ` law (proved)

Let `M` be a matroid on a finite ground set `E`. Every multigraph gives one,
its cycle matroid, whose independent sets are the forests. Give each element
`g` a weight `w_g`, and let `Z(w) = Σ_{I independent} Π_{g∈I} w_g`. For
distinct elements `e, f`, let `R_{ef} = Z_e Z_f − Z Z_{ef}`, the
multivariate Rayleigh difference. Here `Z_e` is the sum over independent sets
containing `e`, and so on. Let `c(e, f)` be the least size of a circuit
containing both `e` and `f`, with `c = ∞` if there is none. A loop is its
own component and lies in no circuit with another element, so for a loop the
theorem gives `R ≡ 0`. Let `N(e, f)` be
the number of circuits of size `c(e, f)` that contain both.

**Theorem.**

(i) If no circuit contains both `e` and `f`, then `R_{ef} ≡ 0`.

(ii) Otherwise, every monomial of `R_{ef}` has total degree at least
`c(e, f)`. The degree-`c` part is `w_e w_f Σ_C Π_{g ∈ C∖{e,f}} w_g`, summed
over the circuits `C` of size `c` that contain `e` and `f`.

In particular, with all weights equal to `λ`:

    R_{ef}(λ) = N(e, f) λ^{c(e,f)} + O(λ^{c(e,f)+1}).

For a graph, this says `P_Z(λ) = R/λ² = N λ^{L−2} + O(λ^{L−1})`. Here `L` is
the length of a shortest cycle through `e` and `f`, and `N` is the number of
such shortest cycles.

**Corollary.** For every finite multigraph, and every pair of edges in a
common block (a loop is its own block; two distinct edges in one block lie on a common cycle), the `λ`-weighted forest measure makes `e` and `f` strictly
negatively correlated for all sufficiently small `λ > 0`. The same holds for
every matroid and every pair of elements in a common connected component.
Edges in different blocks are independent.

This complements the large-`λ` analysis of Çiçeksiz–Ravichandran
(arXiv:2610.00549, Corollary 1.7). There, negative correlation holds for all
large enough `λ` unless an equipotential condition holds. It says nothing about intermediate `λ`, and nothing about
`λ = 1` in particular.

*Proof.*

**Identity.** For independent `Y ⊆ E ∖ {e, f}`, let `a(Y)`, `b(Y)`, `c(Y)`
indicate that `Y + e`, `Y + f`, `Y + e + f` are independent. Let `Z'`,
`Z'_a`, `Z'_b`, `Z'_c` be `Σ_Y w^Y` weighted by `1`, `a`, `b`, `c`. Then

- `Z = Z' + w_e Z'_a + w_f Z'_b + w_e w_f Z'_c`,
- `Z_e = w_e (Z'_a + w_f Z'_c)`,
- `Z_f = w_f (Z'_b + w_e Z'_c)`,
- `Z_{ef} = w_e w_f Z'_c`.

Expanding gives

    R_{ef} = w_e w_f Q,   Q := Z'_a Z'_b − Z' Z'_c,

where `Q` does not involve `w_e` or `w_f`.

(i) Suppose `e` and `f` lie in different connected components `A ∋ e` and
`B ∋ f`. Distinct elements lie in a common circuit iff they lie in the same
component (Oxley, *Matroid Theory*, Prop. 4.1.2). Independent sets split along the components, so `a(Y)`
depends only on `Y ∩ A`, `b(Y)` only on `Y ∩ B`, and `c = ab`. The weighted
sums factor over the components, so `Z'_a Z'_b = Z' Z'_c`, and `Q ≡ 0`.

(ii) Let `w^μ` be a monomial of `Q` with nonzero coefficient, and let
`S ⊆ E ∖ {e, f}` be its support. Setting `w_g = 0` for `g ∉ S` keeps that
coefficient. It also turns `Q` into the corresponding polynomial of the
restriction `M | (S ∪ {e, f})`. By (i), `e` and `f` lie in a common circuit
of this restriction. That circuit has size at most `|S| + 2`, so
`|μ| ≥ |S| ≥ c(e, f) − 2`, and every monomial of `R_{ef} = w_e w_f Q` has
degree at least `c(e, f)`.

If `|μ| = c − 2`, then `|S| = |μ|`, so `μ` is square-free. Moreover,
`S ∪ {e, f}` is a circuit `C` of size `c` containing `e` and `f`. On `M | C`,
every proper subset of `C` is independent, so
`Z'_a = Z'_b = Z' = Π_{g ∈ S}(1 + w_g)` and `Z'_c = Z' − w^S`. Hence
`Q = Z' w^S`, whose lowest term is `w^S`, with coefficient 1.

Conversely, take any circuit `C` of size `c` through `e` and `f`, and set
`w_g = 0` off `S = C ∖ {e, f}`. Then the coefficient of `w^S` in `Q` equals
its coefficient in the restriction's `Q`, which is 1. Different circuits give
different supports. All degree-`c` coefficients are `+1`, so nothing cancels
when every weight is set to `λ`, and the univariate lowest term is
`N λ^c`. ∎

**Corollary 2 (large-`λ` law for connected subgraphs).** Let `G` be connected,
with `m` edges, and let `e ≠ f`. For a loop `e`, set `G/e := G − e`. Then
`C_e = λ C_{G/e}` still holds, and `P_C ≡ 0`. Let `c*` be the least size of a bond (a
minimal edge cut) containing both, and `N*` the number of such bonds. Then

    P_C(λ) = N* λ^{2m − c* − 2} + (lower powers of λ).

If no bond contains both, then `P_C ≡ 0`. So the `λ`-weighted connected
spanning subgraph measure (the `q → 0` random-cluster model) is strictly
negatively correlated for all sufficiently large `λ`, whenever `e` and `f`
lie in a common block.

*Proof.* Complementation `A ↦ E ∖ A` maps the connected spanning edge sets
onto the independent sets of the bond matroid `M*(G)`. So
`C_G(λ) = λ^m I*(1/λ)`, where `I*` is the independence polynomial of `M*`.
The covariance of `1_{e∈A}` and `1_{f∈A}` equals that of the complementary
indicators. Since `Cov = −R/(normaliser)²` in both models, this gives
`R_C(λ) = λ^{2m} R*(1/λ)`. The theorem applied to `M*` gives
`R*(μ) = N* μ^{c*} + O(μ^{c*+1})`. It applies to every element, including
the loops of `M*`, which are the bridges of `G`. The circuits of `M*` are
the bonds. Finally, `P_C = R_C / λ²`. The strict-correlation statement uses
the fact that `M` and `M*` have the same components, so a common block means
a common bond. ∎

Corollary 2 matches all 37,531 edge pairs of the 2-connected graphs with at
most 7 vertices (`cnc -v` output against an enumeration of bonds). The gate
re-checks it for at most 6 vertices.

**Probabilistic form.** For a graph with equal weights, the identity gives

    P_Z = Z'² (E'[a] E'[b] − E'[c]) = Z'² (E'[d] − Cov'(a, b)),

where `d = ab − c ≥ 0` and the expectations are under the arboreal gas on
`G − e − f`. This is the "crossing term minus covariance" form in the
abstract of Çiçeksiz–Ravichandran. We have not matched it to a numbered
result there.

**Checks.**

- The law holds on all 37,531 pairs of all 2-connected graphs with at most 7
  vertices, comparing the C output with an independent enumeration of the
  cycles through `e` and `f`. The 8-vertex result is in
  `evidence/small_lambda_law.json`.
- It holds on 5,040 element pairs of random binary and ternary matroids and of
  uniform matroids.
- The gate re-checks it on all graphs with at most 6 vertices and on random
  matroids.

**Coefficientwise nonnegativity is graph-specific.** For graphs with at most
9 vertices, every coefficient of `P_Z` is nonnegative. This fails for
matroids. Take the binary matroid `[I_4 | X]` with
`X = (0111; 1011; 1101; 1111)`. This is our recollection of Oxley's
representation of `S_8`; the identification is not verified here. It has
three 3-circuits, seven 4-circuits, four 5-circuits and 48 bases. Exactly one of its 28
element pairs gives `R_{ef}(λ) = 4λ⁵ + 12λ⁶ − 16λ⁸`. This pair lies in four
5-circuits and in no smaller circuit, and the lowest term is `4λ⁵`, as the
theorem predicts. The polynomial vanishes at `λ = 1` and is
negative for `λ > 1`, which would be consistent with the Seymour–Welsh failure of
negative correlation for the bases of `S_8`. An exhaustive scan of all binary matrices
`[I_4 | A]` with no zero column finds 1,152 (matrix, element pair) instances
with a negative coefficient, many of them isomorphic. None has `R(1) < 0`. The small-`λ` law holds for this matroid, as
the theorem requires. The gate checks both facts.
