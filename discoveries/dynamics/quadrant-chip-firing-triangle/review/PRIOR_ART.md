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
  a mild extension of their Lemma 7.1 (`R(j) → R(j−1)`): it allows the
  central entry of an odd row to exceed the minimal value by one.

**What was read, and the "rectangle".** The HTML of v1 (arXiv:2601.09125v1)
was read for the passages bearing on the calibration; the PDF fetch returns
only the abstract. The word "rectangle" is never formally defined. It is
introduced in §4.3 ("we have a long rectangle with black dots along its
border", "The rectangle is the widest part of the shape"), and recurs in §6.2
("the longest row is the width of the rectangle, which is the bottom part of
the middle section"), §7, §8 and §9. The count this dossier calibrates
against is in §6.2, Example 5, for `n = 9`:

> "Then, we have our rectangular shape with 57 rows that alternate between 12
> and 13, starting with 12."

followed by

> "The total number of rows is 10 + 13 + 57 + 12 = 92."

All four summands are reproduced by the `CALIBRATION` gate. The earlier
recorded discrepancy (our maximal alternating stretch has 59 rows) was an
artifact of comparing two different regions: IKL's bottom triangle begins at
the last longest row, so it shares its first two rows with the alternating
stretch. Since "rectangle" is informal, this is the reading forced by their
own four-part count, not a claim about what they intended.

This dossier extends the check of Conjecture 7.3 from `n ≤ 12` to `n ≤ 34`,
and to every chip count `N ≤ 300,000`. A search finding nothing is not a
novelty determination.
