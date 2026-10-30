# Written argument

Conjecture 7.3 itself is not proved here. This section fixes the reading of
the conjecture, records one proved lemma (§2), and isolates the observed
statement that would complete a proof (§3).

## 1. The model and the reading of Conjecture 7.3

We follow Inagaki–Khovanova–Luo (arXiv:2601.09125). Take `N` chips at the
origin of the directed quadrant `ℤ²_{≥0}`. A vertex with at least two chips
sends one chip to each of `(x+1, y)` and `(x, y+1)`. The process is abelian,
so the number `F(x, y)` of chips passing through `(x, y)` is well defined:
`F(0, 0) = N` and `F(x, y) = ⌊F(x−1, y)/2⌋ + ⌊F(x, y−1)/2⌋`.

Row `i` is the antidiagonal `x + y = i`. On a row this recursion reads
`F'(x) = ⌊F(x−1)/2⌋ + ⌊F(x)/2⌋`, which is translation invariant. The length
of a row is its number of nonzero entries (IKL §6.2). IKL define the bottom
triangle as "the largest set of rows at the bottom of `F` such that each next
row has one fewer entry than the previous one" (§7).

We read "the number of rows in the bottom triangle" as the size of the
maximal final run of rows whose lengths decrease by exactly 1 at each step.
Conjecture 7.3 states that this number equals `max_i len(i) − 1` when
`N = 2^n`. For `N = 512` the lengths end
`…, 12, 13, 12, 11, …, 2`. The run is `13, 12, …, 2`, which has 12 rows, and
the longest row is 13, in agreement with the paper.

## 2. Lemma (thin rows stay thin and shrink) — proved

Call a row `(f_0, …, f_{L−1})` *thin* if `f_k ≤ 2 min(k, L−1−k) + 1` for all
`k`.

**Lemma.** Let a row be thin with `L ≥ 2`, and let `g` be its image. Then
`g_0 = g_L = 0`, and `g_x ≤ 2 min(x−1, L−1−x) + 1` for `1 ≤ x ≤ L−1`.
Consequently, if the image occupies exactly the sites `1, …, L−1` with no
zero entry, then it is a thin row of length `L − 1`.

*Proof.* The image is `g_x = ⌊f_{x−1}/2⌋ + ⌊f_x/2⌋` for `x = 0, …, L`, with
`f_{−1} = f_L = 0`. Thinness gives `f_0, f_{L−1} ≤ 1`, so `g_0 = g_L = 0`.

For `1 ≤ x ≤ L−1`, the bound `⌊(2a + 1)/2⌋ = a` gives
`g_x ≤ min(x−1, L−x) + min(x, L−1−x)`. If `x − 1 ≤ L − 1 − x`, this is at
most `(x − 1) + x = 2(x − 1) + 1`. Otherwise, by symmetry, it is at most
`2(L − 1 − x) + 1`. In the coordinates `x' = x − 1` this is the thinness
bound for a row of length `L − 1`. ∎

The extra hypothesis is needed. A thin row with interior 1's can have an image
with zeros, after which trimming shifts the coordinates; the gate keeps such
a random example as a control. For the rows of `F` the hypothesis holds,
because consecutive lengths differ by exactly 1 (IKL Prop 6.2) and rows have
no interior zeros (IKL Prop 6.1). Both facts are re-checked on every scanned
`N`. Hence, once a row of `F` is thin, every later row is thin and one
shorter.

## 3. What would complete a proof

For every `N` with `4 ≤ N ≤ 3000` (gate `THIN_STRUCTURE`), and on all the
larger scans, the following holds:

**(S)** The first thin row has the maximal length `w`. It is entered by a
length increase, every later row is thin, and the last row has length 2.

Together with §2 and Prop 6.2, (S) implies the conjecture. The rows after the
first thin row have lengths `w, w−1, …, 2`, which is `w − 1` rows. The row
before it has length `w − 1`, so the run stops there. Proving (S) requires
controlling the "middle section" of `F`, which we have not done.
