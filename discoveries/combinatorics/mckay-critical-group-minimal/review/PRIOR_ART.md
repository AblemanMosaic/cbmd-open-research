# Prior art

- **G. Benkart, C. Klivans and V. Reiner, *Chip firing on Dynkin diagrams
  and McKay quivers*, Math. Z. (2018), arXiv:1601.06849.**
  - Theorem 1.3: `K(γ) ↠ (G^{ab})^` for faithful `γ` into `SL_n(ℂ)`.
  - Theorem 1.4 (Theorem 6.13): isomorphism for `SL_2(ℂ)`.
  - Example 6.6: `A_4 ⊂ SO(3)` with `K ≅ ℤ/3 ≅ G^{ab}`. So BKR already knew a
    minimal case with `n = 3`.
  - Proposition 6.12: trivial summands and automorphisms do not change `K`
    (our Lemma 1(a)).
  - **Question 6.11** is the question addressed here.
  - **Proposition 6.19** answers it for abelian groups: `K ≅ Ĝ` iff `n = 2`
    (no trivial summands). The proof is a sketch due to S. Koplewitz. It
    was read from the PDF supplied by the user, after the fetch tools had
    failed.
- **C. Gaetz, *Critical groups of McKay–Cartan matrices*, honors thesis,
  University of Minnesota (June 2016), supervised by V. Reiner. This is the
  closest prior art.**
  - Corollary 4: the order criterion, our Lemma 1(b).
  - Theorem 8: the known minimal pairs. These are the finite subgroups of
    `SL_2(ℂ)` and, among subgroups of `SO(3)`, exactly the cyclic groups,
    `I_2(n)` with `n` odd, `A_4` and `A_5`. Appendix C proves this case by
    case, including `K ≅ (ℤ/4)²` for `I_2(n)` with `n` even and `K ≅ ℤ/4`
    for `S_4`.
  - **Question 2** asks whether these are the only minimal pairs. This is
    exactly the conjecture of this dossier.
  - So the SO(3) classification (our Theorem 4) is **not new**. The new
    contributions here are:
    - the uniform formula `|K(γ)| = 2^{u−1}|G̃^{ab}|` (Proposition 3);
    - the real monotonicity Lemma 2;
    - the computer-assisted answer to Question 2 for `n = 3` (Theorem 9).
    
    This is subject to the caveat that later work answering Question 2 was
    searched for but not found.
- **C. Gaetz, *Critical groups of group representations*, Linear Algebra
  Appl. (2016), arXiv:1606.00798.**
  - Order formula (F3).
  - Subgroups `(ℤ/a)^{m−1}` when `m` classes share the integer value
    `n − χ = a`.
  - The reflection representation of `S_n`.
  - No characterisation of minimal `γ`.
- **A. Agarwal and C. Gaetz, *Differential posets and restriction in critical
  groups*, arXiv:1710.08253.** Restriction and induction maps between
  critical groups. Contains no minimality question.
- **D. Grinberg, J. Huang and V. Reiner, *Critical groups for Hopf algebra
  modules*, arXiv:1704.03778v4 (13 June 2026 corrected version).**
  **Read in full**, all 24 pages, §§1–8 and the references, from the PDF
  supplied by the user after the fetch tools truncated at about 74,000
  characters. Outcome: **it contains none of Lemma A, Proposition B or
  Theorem M.**
  - No arborescence, spanning-tree or matrix-tree statement for the McKay
    quiver occurs anywhere. The single mention of spanning trees is the
    Introduction's remark that for an ordinary graph the critical group's
    "cardinality is the number of spanning trees in the graph".
  - No comparison of `#K` between two modules, and no direct-sum statement:
    nothing in the paper is a monotonicity result.
  - Their Theorem 1.2 (`#K(V) = |(γ/d)(λ_1 ⋯ λ_ℓ)|`) is proved in §5 from
    **Lorenzini's** Proposition 2.1 (their [16]) — exactly the route that
    Proposition B replaces with an adjugate computation.
  - Question 6.9, unreachable by the fetch tools and the reason this source
    was flagged, asks how to test tensor-richness by character theory and
    whether the nullity of `L_V` is described by the simples appearing in
    `V^{⊗k}`. It does not bear on these results.
  - **Near miss, recorded as such.** Equation (5.1), inside the proof of
    their Proposition 5.3, is an adjugate identity:
    `pᵀ adj(C) = sᵀ C adj(C) = det(C) sᵀ`. So the adjugate of a matrix with
    known left and right vectors is a tool the authors use — but applied to
    the **Cartan matrix** `C`, to show that `γ = gcd(p)` is a power of the
    characteristic, not to `L_V`, and with no cofactor or tree reading.
  - Useful to cite rather than competing: Propositions 3.1 and 3.8 (`s` is a
    left-nullvector and `p` a right-nullvector of `L_V`) are the Hopf
    versions of the two relations `M δ = n δ` and `Mᵗ δ = n δ` that
    Proposition B rests on; Proposition 2.2 (`sᵀ p = dim A`) is the version
    of `Σ_v δ_v² = |G|`; Corollary 7.4 (faithful representations of a finite
    group are always tensor-rich) is the general form of the faithfulness
    input to Theorem M.
  - **A Hopf-algebra extension, stated but NOT verified here.** Their
    Propositions 3.1, 3.8 and 2.2 are exactly the three ingredients Lemma A
    and Proposition B use, so for a tensor-rich module over a
    finite-dimensional Hopf algebra one expects
    `#K(V) = γ · A_ε(V)`, where `A_ε(V)` is the weighted arborescence count
    rooted at the trivial module with weights `(M_V)_{ij} p_j / p_i`, and
    `M_{V⊕W} = M_V + M_W` should then give the same monotonicity. This is
    recorded as a direction, not a result: it has not been checked, by hand
    or by machine, and nothing in this dossier depends on it.

- **H. Browne, *Connectivity properties of McKay quivers*,
  arXiv:2003.09502.** Read: the full list of numbered results.
  - Proposition 3.3: the McKay quiver of a faithful representation is
    strongly connected (via Burnside). Used in Theorem M.
  - Proposition 5.2: for faithful `ρ` the quiver's weight vector is the
    dimension vector of the irreducibles; Corollary 2.4, `Γ_ρ(G)` is
    `(dim ρ)`-weightable. This is the relation `M δ = n δ` that Lemma A
    turns into a digraph Laplacian.
  - Lemma 4.1: the dual group acts by quiver automorphisms, used for the
    remark on `A_v = A_0` for one-dimensional `χ_v`.
  - Contains no critical group, arborescence or spanning-tree statement.
- **`CBMD-COMB-CAYLEY-JAC-001`.** The abelian case.
- **H. F. Blichfeldt, *Finite collineation groups* (1917).** The
  classification of finite subgroups of `SL_3(ℂ)` into types A–L. We use it
  as tabulated in **S. S.-T. Yau and Y. Yu, *Gorenstein quotient
  singularities in dimension three*, Mem. AMS 505 (1993)**. Theorem 9 relies
  on two facts from it: the list of primitive groups, and the statement that
  imprimitive irreducible groups are monomial.

Searches in 2026 found no later answer to Gaetz's Question 2, and no
statement of Proposition 3, Lemma 2 or Theorem 9. A search that finds nothing
is not a novelty determination. BKR §6 was read in full (pages 25–29 of the
arXiv v2 PDF); BKR §2, including Remark 2.18 on digraph critical groups and
their arborescence count, was read in full. Gaetz's thesis §§1–5 were read in
full. The one acknowledged gap is the tail of arXiv:1704.03778, recorded
above.
