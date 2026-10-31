# Prior art

- **G. Musiker and S. Nguyen, *Labeled chip-firing on binary trees with
  `2^n − 1` chips*, Ann. Comb. (2023), arXiv 2206.02007.** They introduce the
  model and prove the stable shape and the extreme chips. Liscio's data gives
  all 36,220 stable configurations for 15 chips.
- **R. Inagaki, T. Khovanova and A. Luo, *On chip-firing on undirected binary
  trees*, Ann. Comb. 30 (2026) 439–465, arXiv 2410.00039.**
  - Bounds on the number of stable configurations.
  - The ballot property conjecture (Conjecture 3.16 in print, 3.7 on arXiv),
    checked on the 15-chip data.
  - The conditional ballot bound (Theorem 3.19).
  - Firing counts.
- **R. Inagaki and A. Lin, *Labeled chip-firing on undirected k-ary trees*,
  arXiv 2509.17358 (2025).** The `k`-ary model and Conjecture 5.1, the
  generalized ballot property for `k ≥ 2`. The paper says its validity for
  higher `ℓ` "remains uncertain".

- **Independent literature audit (October 2026).** It traced the whole
  cluster: the IKL directed-tree, permutation-strategy and lattice papers
  (arXiv 2410.23265, 2503.09577 with its DMTCS version, 2506.20656,
  2601.09125), Agrawal et al. (arXiv 2501.06675), Gonzalez-Zugasti, Lynch and
  Snustad (arXiv 2510.27082), Musiker-Nguyen, and the labeled chip-firing
  line of Hopkins, McConville, Propp, Klivans, Liscio and Galashin. It found:
  - both conjectures are open, with no counterexample, proof, withdrawal or
    revision; arXiv 2410.00039 has only a v1, and Conjecture 5.1 is
    unchanged between v1 and v2 of arXiv 2509.17358;
  - the published verification of the ballot property covers only `ℓ = 3, 4`
    (15 chips, Liscio's data), so the certificates here (binary `ℓ = 5..8`,
    ternary `ℓ = 4, 5`, 4-ary `ℓ = 4`) are the first cases tested;
  - the conditional ballot bound (IKL Theorem 3.19, with Lemma 3.18) is the
    downstream casualty; IKL's unconditional zigzag bound (Theorem 3.13)
    survives.
  
  The audit reached the published Annals text through a fetch layer that caps
  verbatim quotation, so it confirmed the statements of Definition 3.14 and
  Theorem 3.19 in fragments rather than reading their proofs, and it could
  not diff v2 and v3 of arXiv 2503.09577 (the published version has no
  conjectures). Citation indexes were unavailable, so the sweep is
  bibliography-based rather than index-complete.

Searches (October 2026) found no counterexample in the literature. Not a
novelty determination.
