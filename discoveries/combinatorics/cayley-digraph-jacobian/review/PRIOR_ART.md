# Prior art

- **G. Benkart, C. Klivans and V. Reiner, *Chip firing on Dynkin diagrams
  and McKay quivers*, Math. Z. (2018), arXiv:1601.06849.**
  - Theorem 1.3: for a faithful representation into `SL_n(ℂ)`, the critical
    group surjects onto the dual of `G^{ab}`.
  - Theorem 1.4: for `SL_2(ℂ)`, it is an isomorphism.
  - For abelian `A`, the McKay quiver is the Cayley digraph treated here.
- **BIRS workshop on sandpile groups, open problems** (compiled by S.
  Hopkins), problem 1.9 (V. Reiner). It states the question for finite
  abelian `A` and sum-zero multisets, and notes that the "if" direction is
  clear.
- **C. Gaetz, *Critical groups of group representations* (2016),
  arXiv:1606.00798.** Gives an order formula `|K(γ)| = (1/|G|) Π_i (n − χ_γ(c_i))`
  and examples, including the cyclic 2-dimensional case `K ≅ ℤ/m`. It does
  not characterise when `K ≅ G^{ab}`.
- **Resolved (0.2.0): the qualitative theorem is prior art.** BKR
  (arXiv:1601.06849v2, §6.2) prove the following as Proposition 6.19, with a
  proof sketch due to S. Koplewitz: for finite abelian `G` and faithful
  `γ : G ↪ SL_n(ℂ)` with no copies of `1_G`, `K(γ) ≅ Ĝ` iff `n = 2`. This is
  the same statement as the theorem here.
  - **Their method:** a Hamilton path in the Cayley digraph (Gallian–Witte)
    gives an injection from `A` into the arborescences directed toward 0,
    which is not surjective when `r ≥ 3`.
  - **Our method is different:** cyclotomic norms, `p`-adic counting and an
    AM–GM bound. Our bounds `|Jac| ≥ (3/2)^{φ(n)} n` and
    `p^{2+v_p(n)} | |Jac|` are not in their sketch.
  - **BIRS problem 1.9** (2015) predates BKR (January 2016). So it was
    answered there.
  - **C. Gaetz's honors thesis** (Minnesota, 2016) restates Proposition 6.19
    in a remark after its Question 2.
- Whether the quantitative bounds are known was not searched specifically.
  This is not a novelty determination.
