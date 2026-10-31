# Written argument

## Setting

Let `A` be a finite abelian group of order `n ≥ 2`, and `S` a multiset of `s`
nonzero elements of `A` with `Σ_{x∈S} x = 0`. Assume `S` generates `A`.
Reiner's text leaves this hypothesis implicit. It is the faithfulness of the
corresponding McKay representation, which BKR's surjection needs.

Without it the digraph is disconnected and the reduced-Laplacian cokernel is
infinite. Under the alternative convention "torsion of the cokernel of the
full Laplacian", `A = (ℤ/2)²` with `S = {(1,0), (1,0)}` gives a torsion group
isomorphic to `A`, although `A` is not cyclic. So the hypothesis cannot be
dropped. Let `G` be the
Cayley digraph `Cay(A, S)`, with one arc `g → g + x` for each `x ∈ S`, counted
with multiplicity. `G` is Eulerian (every in- and out-degree is `s`) and
strongly connected. Its Jacobian `Jac(G)` is the cokernel of its reduced
Laplacian; for an Eulerian digraph this does not depend on the deleted
vertex. Here `L f(g) = s f(g) − Σ_{x∈S} f(g + x)`.

**Question (V. Reiner; BIRS sandpile-group workshop, problem 1.9).** There
is always a surjection `Jac(G) ↠ A` (Benkart–Klivans–Reiner). Is
`Jac(G) ≅ A` if and only if `A ≅ ℤ/nℤ` and `S = {a, −a}` for a generator
`a`?

**Prior art.** Yes. This is Proposition 6.19 of Benkart–Klivans–Reiner
(arXiv:1601.06849v2), with a combinatorial proof sketch due to S. Koplewitz:
a Hamilton-path injection from `A` into the arborescences. The proof below is
an independent algebraic one, and it also gives quantitative bounds.

**Theorem.** If `A` is not cyclic, or if `s ≥ 3`, then `|Jac(G)| > |A|`.
Quantitatively:

- if `A` is cyclic and `s ≥ 3`, then `|Jac(G)| ≥ (3/2)^{φ(n)} · n`;
- if the `p`-part of `A` is not cyclic, then `p^{2 + v_p(n)}` divides
  `|Jac(G)|`.

The "if" direction is classical. `S = {a, −a}` with `a` a generator makes
`G` the undirected `n`-cycle, whose Jacobian is `ℤ/nℤ`. For the "only if"
direction, `s = 2` and `Σ S = 0` force `S = {a, −a}`, and generation forces
`a` to be a generator. So it suffices to prove `|Jac(G)| > n` when `A` is
not cyclic or `s ≥ 3`.

## Lemma 1 (spectrum and the matrix-tree theorem)

`L` acts on functions on `A` by convolution, so it is diagonalised by the
characters `χ ∈ Â`, with eigenvalues

    λ_χ = s − Σ_{x∈S} χ(x) = Σ_{x∈S} (1 − χ(x)).

`λ_χ = 0` iff `χ` is trivial on `⟨S⟩ = A`. For an Eulerian digraph, the
product of the nonzero Laplacian eigenvalues equals
`Σ_r κ_r = n κ`. Here `κ_r` is the number of spanning arborescences oriented
towards `r`, and `κ = κ_r` does not depend on `r`. Since
`|Jac(G)| = det(reduced L) = κ`,

    n · |Jac(G)| = Π_{χ ≠ 1} λ_χ.

## Lemma 2 (Galois orbits)

Let `χ` have order `d`. Its Galois orbit is `{χ^k : k ∈ (ℤ/d)^×}`; it has
`φ(d)` elements, all with kernel `H = ker χ`, and `A/H ≅ ℤ/d`. Conversely,
each subgroup `H ≠ A` with `A/H` cyclic gives exactly one orbit. Since
`λ_{χ^k} = σ_k(λ_χ)`, where `σ_k` is the automorphism `ζ_d ↦ ζ_d^k` of
`ℚ(ζ_d)`, the product over an orbit is the norm

    N_H := Π_{k ∈ (ℤ/d)^×} λ_{χ^k} = N_{ℚ(ζ_d)/ℚ}(λ_χ).

This is a positive integer: it is a nonzero rational integer, and the
conjugates pair as `λ_{χ^{−k}} = conj(λ_{χ^k})`, or are real when
`d ≤ 2`. Hence `n |Jac(G)| = Π_{H} N_H`, over the subgroups `H ≠ A` with
cyclic quotient.

## Lemma 3 (prime-power orbits contribute `p²`)

If `A/H ≅ ℤ/p^k` with `k ≥ 1`, then `p² | N_H`.

*Proof.* Write `χ(x) = ζ^{m_x}`, where `ζ = ζ_{p^k}` and `0 ≤ m_x < p^k`,
and let `π = 1 − ζ`. Then
`λ_χ = Σ_x (1 − ζ^{m_x}) = π · Σ_x [m_x]_ζ`, where
`[m]_ζ = 1 + ζ + … + ζ^{m−1}`. Since `ζ ≡ 1 (mod π)`, we get
`Σ_x [m_x]_ζ ≡ Σ_x m_x (mod π)`. Because `Σ S = 0`, we have
`χ(Σ_x x) = 1`, so `Σ_x m_x ≡ 0 (mod p^k)`, and `p ∈ (π)`. Hence
`λ_χ ∈ (π)²`, and `N(π) = p` gives `p² | N(λ_χ)`. ∎

## Lemma 4 (an AM–GM lower bound)

Let `χ` have order `d`, and suppose three distinct members `x_1, x_2, x_3`
of the multiset `S` satisfy `χ(x_j) ≠ 1`; their values may coincide. Then

    N(λ_χ) ≥ (3/2)^{φ(d)} · Π_{j=1}^{3} N(1 − χ(x_j))^{2/3},

where `N = N_{ℚ(ζ_d)/ℚ}`. Each `N(1 − χ(x_j))` is a positive integer. It is
at least `p` when `d = p^k`, because `1 − (a primitive p^{k'}-th root)` has
norm `p` in its own cyclotomic field. Hence:

- `N(λ_χ) ≥ (3/2)^{φ(d)} p²` when `d = p^k`;
- `N(λ_χ) ≥ (3/2)^{φ(d)}` in general.

*Proof.* For each conjugate,
`|λ_{χ^k}| ≥ Re λ_{χ^k} = Σ_{x∈S} (1 − cos θ_x)`, and every term is `≥ 0`.
Keeping only `x_1, x_2, x_3` and using
`1 − cos θ = |1 − e^{iθ}|²/2` and AM–GM gives

    |λ_{χ^k}| ≥ (3/2) Π_j |1 − χ^k(x_j)|^{2/3}.

Multiplying over `k ∈ (ℤ/d)^×` gives the claim. ∎

## Proof of the Theorem

Suppose `|Jac(G)| = n`, so `Π_H N_H = n²` (Lemmas 1 and 2).

**Step 1: ruling out non-cyclic `A`.** Fix a prime `p` with `A_p ≅ ⊕_{i=1}^{r} ℤ/p^{e_i}`.
Write `e = Σ e_i`, so `v_p(n) = e`. Under the duality `H ↦ H^⊥`, the
subgroups `H` with `A/H` cyclic of order `p^k` (`k ≥ 1`) correspond to the
nontrivial cyclic subgroups of `p`-power order in `Â ≅ A`. Their number `c_p`
is at least `e`, from the subgroups `⟨p^{e_i − j} u_i⟩` along the coordinate
axes, `1 ≤ j ≤ e_i`. If `r ≥ 2`, the subgroup
`⟨p^{e_1−1} u_1 + p^{e_2−1} u_2⟩` gives one more, so `c_p ≥ e + 1`. By
Lemma 3, `v_p(Π_H N_H) ≥ 2 c_p ≥ 2e + 2 > 2e = v_p(n²)`, a contradiction.
So every `A_p` is cyclic, and so is `A`. The same count does not use `|Jac| = n`, so it proves the stated
divisibility `p^{2+v_p(n)} | |Jac(G)|` for noncyclic `A_p`. In particular
`|Jac(G)| ≥ p² n`.

**Step 2: ruling out `s ≥ 3` for cyclic `A`.** Let `A = ℤ/n` and suppose `s ≥ 3`. Take `χ` faithful, of order
`d = n`. Then `χ(x) ≠ 1` for every `x ∈ S`, since the elements of `S` are
nonzero.

- **`n` not a prime power.** There is one prime-power orbit for each prime
  power `p^k` dividing `n` (`k ≥ 1`). By Lemma 3 these orbits together
  contribute at least `Π_{p^k | n} p² = Π_p p^{2 v_p(n)} = n²`. So every other
  orbit, including the faithful one, must have norm 1. Lemma 4
  gives `N(λ_χ) ≥ (3/2)^{φ(n)} > 1`, a contradiction.
- **`n = p^e`.** The orbits are `d = p, …, p^e`. Each has norm divisible by
  `p²`, and the product is `p^{2e}`, so each norm equals `p²`. Lemma 4 gives
  `N(λ_χ) ≥ (3/2)^{φ(n)} p² > p²` for the faithful orbit, a contradiction.

In both cases the same estimates give
`n |Jac(G)| ≥ n² (3/2)^{φ(n)}`, which is the quantitative bound. ∎

## Remarks

- The sum-zero hypothesis enters only through Lemma 3. Lemma 4 is a
  general lower bound for norms of sums of terms `1 − (root of unity)`.
- Zero elements of `S` (loops) do not change `L`, so they may be allowed.
  The conclusion then concerns the nonzero part of `S`.
- The argument uses only `|Jac(G)|`. The quantitative bounds show how far
  `Jac(G)` is from `A` in general.

## Remark: the non-abelian analogue fails

For a finite group `G` and a faithful representation `γ : G → SL_n(ℂ)`, BKR
prove that the critical group `K(γ)` surjects onto the dual of `G^{ab}`
(their Theorem 1.3). When `n = 2` this surjection is an isomorphism (their
Theorem 1.4). The theorem above says that for abelian `G`, an isomorphism
forces `γ` to be a sum of trivial characters and one pair `{a, −a}`.

For non-abelian `G` the analogous statement is false:

- For `A_4 ⊂ SO(3) ⊂ SL_3` (the rotations of a tetrahedron),
  `K(γ) ≅ ℤ/3 ≅ A_4^{ab}`.
- For `A_5 ⊂ SO(3)` (the rotations of an icosahedron), `K(γ)` is trivial,
  and so is `A_5^{ab}`.
- For the octahedral group `S_4 ⊂ SO(3)`, `K(γ) ≅ ℤ/4`, while
  `S_4^{ab} ≅ ℤ/2`.

All three groups act through irreducible 3-dimensional representations.
`verification/reference/nonabelian_examples.py` computes these by Smith normal
form of the reduced McKay–Cartan matrix, built from tensor-product
multiplicities. They agree with the order formula
`|K(γ)| = |G|^{−1} Π_{c ≠ 1} (n − χ_γ(c))` (Gaetz):

- `A_4`: `4·3·3/12 = 3`;
- `S_4`: `4·3·4·2/24 = 4`;
- `A_5`: `4·3·5/60 = 1`.

In these examples every group element has at most two eigenvalues different
from 1, so the AM–GM step (Lemma 4) has nothing to bite on. Lemma 3 also
weakens, because the norm over a Galois orbit of conjugacy classes can drop to
`p` once the classes `g^k` fuse. Which pairs `(G, γ)` give `K(γ) ≅ (G^{ab})^` in general is BKR's
Question 6.11. Dossier `CBMD-COMB-MCKAY-MIN-001` proposes a conjectural answer
and proves it for orthogonal 3-dimensional representations.
