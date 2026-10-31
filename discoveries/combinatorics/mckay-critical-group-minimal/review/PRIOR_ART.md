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
  modules*, arXiv:1704.03778.** The Hopf algebra generalisation. Contains no
  minimality question.
  - **Read:** §§1–6 of the arXiv PDF, through the proof of Theorem 1.4
    (including Questions 5.2 and 5.11). Theorem 1.2 gives `#K(V)` from the
    eigenvalues; Corollary 1.3 is the group case of (F3); Propositions 3.1
    and 3.8 are the two eigenvector relations used in Proposition B.
    No arborescence or spanning-tree statement, and no comparison between
    the critical groups of two different modules, occurs in what was read.
  - **Not read: the end of §6 onwards** — Question 6.9, and whatever
    follows. The author's own copy of the PDF is `robots_disallowed`, and
    both the arXiv PDF and the ar5iv HTML truncate at about 74,000
    characters, mid-proof of (v) ⇒ (i). The PDF has been requested from the
    user. **Until it is read, no novelty is asserted for Lemma A,
    Proposition B, Theorem M or its corollaries.** They are recorded here as
    proved, not as new. Their proofs use only `M δ = n δ`, `Mᵗ δ = n δ` and
    additivity of `M`, so the same argument should run in that paper's
    setting with `δ` replaced by the dimension vectors of the simples and of
    the indecomposable projectives — which is one reason this is the one
    source that could plausibly already contain them.
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
