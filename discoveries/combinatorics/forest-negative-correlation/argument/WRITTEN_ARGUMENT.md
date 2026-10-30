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
`X_{ef} = λ² X_{G/e/f}`. If `e` and `f` are parallel copies, then `Z_{ef} = 0`
and `C_{ef} = λ² C_{(G/e) − f}`, where `f` has become a loop of `G/e`. Thus
negative correlation is equivalent to

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

Hence the conjectures hold for all graphs on at most `n` vertices iff they
hold for all 2-connected graphs on at most `n` vertices. A bridge carries only
one edge. The same reduction holds for multigraphs.

## 3. Completeness of the enumeration

The 2-connected graphs come from `geng -C` (nauty 2.8.8, built from the
source shipped in pynauty 2.8.8.1). Its counts 1, 3, 10, 56, 468, 7123,
194066 for 3..9 vertices match OEIS A002218. Within each graph, every
unordered pair of distinct edges is tested, without symmetry reduction. The
multigraph runs use `multig` on the same lists.
