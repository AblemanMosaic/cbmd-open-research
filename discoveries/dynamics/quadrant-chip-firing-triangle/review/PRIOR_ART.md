# Prior art

- **R. Inagaki, T. Khovanova and A. Luo, *Chip-firing on the lattice of
  nonnegative integer points*, arXiv:2601.09125.** They introduce the model
  with `2^n` chips at the origin. They prove the structural results used here,
  including Prop 6.1 (row shape), Prop 6.2 (consecutive lengths differ by
  exactly 1), and Lemma 7.1 and Prop 7.2 (minimal rows `R(j)`). Their
  Conjecture 7.3, on the bottom triangle, was checked by computing `F(x, y)`
  for `n ≤ 12`. Their data are in OEIS A389565, A390129 and A390355 and in
  their GitHub repository.
- Their minimal rows `R(j)` are thin in the sense of §2. The thin-row lemma is
  close in spirit to their Lemma 7.1 and may be implicit there.

This dossier extends the check of Conjecture 7.3 from `n ≤ 12` to `n ≤ 34`,
and to every chip count `N ≤ 300,000`. It is not a novelty determination.
