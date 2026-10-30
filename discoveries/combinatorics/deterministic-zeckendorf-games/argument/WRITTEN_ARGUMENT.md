# Deterministic Zeckendorf games: written argument

## 1. Merging moves and the length

A merging move (adding two `1`s, or adding two consecutive terms) lowers the
number of pieces by one. A split keeps it. Play starts with `n` pieces and ends
with the `Z(n)` pieces of the Zeckendorf decomposition, which is the only
terminal position (Baird-Smith et al. 2018). So every play has exactly
`n − Z(n)` merging moves, and its length is `n − Z(n) + #splits`.

## 2. An exact length identity

Look for weights `w` such that the potential `Φ = Σ_pieces w(index)` has these
properties:

- adding two `1`s changes `Φ` by `−1`;
- every split changes `Φ` by `−1`;
- adding consecutive terms into index `j` changes `Φ` by `−(j − 1)`.

The conditions are:

- `w(2) − 2w(1) = −1`;
- `w(1) + w(3) − 2w(2) = −1`;
- `w(i−2) + w(i+1) − 2w(i) = −1` for `i ≥ 3`.

Take `w(1) = 0`. Then `w(i) = −c_i` with `c_1 = 0, c_2 = 1, c_3 = 3` and
`c_{i+1} = 2c_i − c_{i−2} + 1`. In closed form, `c_i = F_{i+2} − i − 2`. This follows from `c_{i+1} − c_i = F_{i+1} − 1` together with `Σ_{t ≤ i} F_t = F_{i+2} − 2`. For an add into index `j`,
`w(j) − w(j−1) − w(j−2) = −(c_j − c_{j−1} − c_{j−2}) = −(j − 1)`, directly
from the closed form and `F_{j+2} = F_{j+1} + F_j`.

Summing over a play from `Φ = 0` (all pieces at index 1) to the Zeckendorf
decomposition:

`−Σ_{Zeck} c_i = −(#ones-adds + #splits) − Σ_adds (j − 1)`,

so

`L = #ones-adds + #splits + #adds = Σ_{i ∈ Zeck(n)} c_i − Σ_adds (j − 2)`.

Every add produces `j ≥ 3`, so each add costs at least one move against the
bound `Σ c_i`. This is the "exact formula in terms of the number of each move
type" of Cusenza et al. (2021), written so that only the add moves appear. The
gate `LENGTH_IDENTITY` checks it for all four games and every `n ≤ 3000`.

## 3. Split Smallest at `F_k − 1`

Two results of Cusenza et al. are used:

- **Theorem 1.2:** Split Smallest realises a longest game.
- **Theorem 1.4:** a play using only splits and ones-adds exists exactly when
  `n = F_k − 1`.

A play with no adds has length `Σ c_i` by §2, and §2 shows no play is longer.
So at `n = F_k − 1` the longest length is `Σ_{Zeck(F_k − 1)} c_i`, and SS has
no add moves there. By §1 its split count is that length minus the
`n − Z(n)` merging moves:

`S_SS(F_k − 1) = Σ_{Zeck(F_k − 1)} c_i − (F_k − 1 − Z(F_k − 1))`.

The Zeckendorf decomposition of `F_k − 1` is `F_{k−1} + F_{k−3} + …` (game
indexing, `F_1 = 1`). Simplifying with Fibonacci and arithmetic sums gives a
closed form. It is cleanest in the shifted sequence `G_k = F_{k+1}`
(`G_0 = 1, G_1 = 2`):

`S_SS(G_k − 1) = G_{k+1} − (2k² + 8k + 15 + (−1)^k)/8`.

The simplification is routine and not written out here; the gate
`SS_FIBONACCI_closed_form` checks the closed form for every `G_k ≤ 3000`.
This section rests on the cited Theorems 1.2 and 1.4; the dossier itself
checks that SS is a longest game only for `n ≤ 40` (gate `LONGEST`). The
equality `S_SS(G_k) = S_SS(G_k − 1)` is checked, not proved.

## 4. Split Smallest: regularity (conjecture) and exact length (proved)

Write `S(n)` for the SS split count. Its Hankel matrices over Zeckendorf
words of lengths 6, 7 and 8 have rank 6. Separately, a 9-dimensional linear
representation over the blocks `0` and `10` (a trailing `1` is read by a
separate output vector) was fitted on prefixes of length ≤ 10 and suffixes of
length ≤ 8. It was not minimised, so its dimension is an upper bound, not the
rank. It reproduces `S(n)` for every `n ≤ 120,000`
(`evidence/ss_large_range.json`). If it is exact, the SS length
`n − Z(n) + S(n)` is Fibonacci-regular, since `Z(n)` is.

The winner is the parity of the length. The representation has entries with
denominator 2, so it cannot simply be reduced mod 2. A finite parity automaton
would need a separate argument (an integer representation, or the exact
formula below); none is claimed here.

**The block law.** `S(F_k + m) = S(F_k) + S(m) + D_{k mod 2}(m)` for `k ≥ 4`
and `m < F_{k−1}`. This is the shape a structural proof would take.

**The counting phase (proved).** Write the pieces at indices ≥ 2 as a binary
word `w`, with index 2 on the right. Let `𝓛` be the set of binary words that
contain no `00`, except possibly one `00` followed only by `1`s.

*Lemma.* While at least two `1`s remain, SS repeats one step: add the two
`1`s into a `2`, then split until no duplicate remains. If `w ∈ 𝓛` before the
step, then afterwards the word is the next word of `𝓛` in increasing binary
order, and the step made exactly `r` splits, where `r` is the number of
trailing `1`s of `w`.

*Proof.*
- **No other move intervenes.** SS prefers splits, then adding `1`s, then
  adding consecutive terms. After normalisation there is no duplicate, so
  while two `1`s remain the next move is the insertion.
- **Case `r = 0`.** The insertion turns the last bit from `0` to `1`. There is
  no split. The result is `w + 1`. It lies in `𝓛`: a final `y00` becomes
  `y01`, which removes that `00`, and nothing else changes.
- **Case `r ≥ 1`.** Write `w = x 0 1^r`. The duplicate at position 0 (index 2)
  splits into position 1 and returns an `F_1`. A duplicate at position 1
  (index 3) splits into position 2 and returns an `F_1`. A duplicate at a
  position `p ≥ 2` (index `≥ 4`) splits into `p + 1` and `p − 2`.
- **The carry.** The carry runs up through the `r` ones. Each deposit at
  `p − 2` lands on a position the carry has already cleared, and no later
  split touches it. So no new duplicate arises.
- **Case `r ≥ 2`.** The result is `x 1 0 0 1^{r−2}`, after exactly `r` splits.
  The words strictly between `x 1 0^r = w + 1` and `x 1 0 0 1^{r−2}` all
  contain `00` followed by a `0`. So are `x 1 0^r` itself when `r ≥ 3`, and
  `x 1 0 0` is the result itself when `r = 2`. So none of them is in `𝓛`.
- **Case `r = 1`.** The result is `x 1 0 = w + 1`.
- **Membership.** In every case the result is in `𝓛`. Its only possible
  `00` is the new one, because the `00` of `w`, if any, was the one consumed by
  the carry. ∎

Words of `𝓛` without `00` are exactly the *lazy* Fibonacci representations
(no two consecutive zeros). So the counting phase of Split Smallest runs the
lazy Fibonacci counter, passing through a transient `00 1^j` tail after each
long carry. The gate `COUNTER_lazy_language_radix_order` checks the lemma for
20,000 steps.

**Where the counting phase stops.** Every move conserves the total value, so
at each visited word the number of `1`s is `n − val(w)`. A step uses two
`1`s and returns `min(r, 2)`, so the value along `𝓛` is non-decreasing (a
step with `r ≥ 2` leaves it unchanged) and rises by at most 2 per step. The
visited words are exactly `𝓛` in increasing order, starting from the empty
word. So the phase stops at the first word *in that order* with value at
least `n − 1`, and then `a = n − val(w*) ∈ {0, 1}`.

A step with `r ≥ 2` returns as many `1`s as it uses, so the phase can only
stop after a step with `r ≤ 1`. Every such step ends in a lazy word (no `00`):

- from a lazy word, `x0 → x1` and `x01 → x10` (here `x` cannot end in `0`,
  since `x01` has no `00`);
- from a tail word, `x100 → x101` and `x1001 → x1010`.

So the end phase always starts from a lazy representation with at most one
`1` left over. That it never adds two `1`s is proved in the run lemma below.
The end-phase formula needs the stopping word to be lazy: on words that still
contain `00` it fails (e.g. `w = 11001`, `a = 1`).

**The end phase (proved).** Let the counting phase stop at the lazy word
`w`, with `a ∈ {0, 1}` ones left. Read `w` as blocks of `1`s separated by
single `0`s, and process the blocks from the low end. Let `γ` be a carry,
initially `γ = a` if `w` ends in `1` and `γ = 0` otherwise. A block of length
`k` contributes `⌊(k − 1 + γ)²/4⌋` splits, and then `γ ← [k + γ ≥ 2]`. The end
phase makes exactly the sum of these contributions.

*Lemma (a run).* Suppose single pieces occupy the consecutive indices `q, …,
q + m − 1`, with `m ≥ 3`. Suppose indices `q − 1` and `q + m` are empty, and
the pieces below `q − 1` contain no duplicate and no consecutive pair. Suppose
there is at most one `F_1`. Then SS does the following:

- it adds the pair `(q, q + 1)` into `q + 2`;
- it splits at `q + 2, q + 3, …, q + m − 1` in that order;
- it leaves a run of length `m − 2` at `q`, and one piece at `q + m`.

*Proof.*
- **The add.** There is no duplicate, at most one `F_1`, and no consecutive
  pair below `q` (index `q − 1` is empty). So `(q, q + 1)` is the smallest
  consecutive pair. Pieces above the run do not matter: SS takes the smallest
  pair. (The weaker hypothesis "nothing below is consecutive with `q`" is not
  enough: with pieces at `2, 3, 5, 6, 7`, SS adds `(2, 3)` first.)
- **The cascade.** The add doubles index `q + 2`. A split at index `i`
  (always `i ≥ 3` here) moves one piece to `i + 1` and one to `i − 2`. The
  piece at `i − 2` lands on a position emptied earlier in the cascade: `q` and
  `q + 1` were emptied by the add, and each later deposit position by the
  split before it. So exactly one duplicate exists at each moment, at `i + 1`,
  and it is the smallest.
- **The end.** The cascade stops at `q + m − 1`, whose split puts a piece on
  the empty `q + m`.
- **What remains.** The deposits fill `q, …, q + m − 3`.
- **No early ones-add.** The number of `F_1` pieces never reaches 2. A split
  at index 3 deposits an `F_1` only when the run starts at `q = 1`, which
  means the leftover one has just been consumed by the add. ∎

*Proof of the end phase.*
- **A block becomes a run.** The lowest block, together with the carry
  piece directly below it, is a run of length `m = k + γ`. The carry piece is
  the leftover `F_1` (when the block starts at index 2), or the piece pushed
  out of the previous block.
- **Peeling the run.** Applying the lemma repeatedly peels the run:
  `m → m − 2 → …`. Each round puts one piece two above the previous one, so the
  pushed-out pieces end up alternating.
- **The last round.** A run of length 2 is added into one piece. A run of
  length 1 stays.
- **The count.** The splits number `(m − 2) + (m − 4) + … = ⌊(m − 1)²/4⌋`.
- **The carry out.** A piece lands just above the block (on the separating
  `0`) exactly when `m ≥ 2`. It is consecutive with the next block, so the
  next block starts with `γ = 1`.
- **The hypotheses hold at every round.** Inside a block, each round leaves
  the run at `q` with `q + m − 2` empty, and the pushed-out pieces at
  `q + m, q + m − 2, …` are pairwise two apart. After a block, the processed
  pieces are those pushed-out pieces plus the final add result or lone piece;
  the topmost is the carry, which is part of the next run, and the index just
  below it is empty. So below the next run's start there is an empty cell and
  no duplicate or consecutive pair.
- **Order of moves.** SS always works on the smallest consecutive pair, and the
  invariant above puts no pair below the current run, so it finishes each
  block before touching the next one.
- **The base.** If `w` ends in `0` and `a = 1`, the `F_1` is not consecutive
  with anything and stays, so `γ = 0`. ∎

**The exact length.** Combine the two phases. Let `w*` be the first word of
`𝓛` (in increasing order) whose value is at least `n − 1`. By the counting
lemma, the counting phase stops exactly there. Then

`S_SS(n) = Σ_{w ∈ 𝓛, w < w*} tr₁(w) + E(w*, n − val(w*))`, and
`L_SS(n) = n − Z(n) + S_SS(n)`,

where `tr₁` counts trailing `1`s and `E` is the end-phase sum. This is an
exact, computable formula for Split Smallest's length: a sum over the counter
language below `w*` (about `n` terms), not a closed form, and it says nothing
yet about asymptotics. The winner is the parity of `L_SS(n)`. The gates `END_PHASE_block_formula` and
`EXACT_FORMULA_matches_simulation` check the two lemmas. The large-range
evidence checks the assembled formula against simulation for every
`n ≤ 120,000`.

The 9-dimensional representation of §4 remains an observed compression of
this formula. Its exactness for all `n` is still conjectural; the formula above
is the proved statement.

## 5. Combine Smallest

The CS split count has Hankel rank 13, 21 and 34: full rank at every tested
length. It is not Fibonacci-regular of small rank in the tested window. Its
length ratio is `1.206474` at `n = 10^6` and `1.206480` at `n = 9,227,465`,
consistent with Li et al.'s conjectured `≈ 1.20647`.

## 6. Winners

- **CL and SL:** the length is `n − Z(n)`, so Player 1 wins exactly when
  `n − Z(n)` is odd.
- **SS:** Player 1 wins when `L_SS(n)` from the exact formula of §4 is odd. For `n ≤ 60`
  the winners are `212112221111211121121222212212121122212212111112212211122221`
  (digit = winning player).
- **CS:** by direct simulation only.

## 7. Review

An independent review (fresh agent, own simulator, no dossier code) found the
exact formula proved up to fixable gaps. This version makes those fixes:

- the run lemma's hypothesis was too weak and is strengthened;
- the `r = 0` case was misstated;
- the conservation invariant and "first in order" point are now explicit;
- §3's indexing clash and missing `n − Z(n)` step are corrected;
- the claims about a mod-2 automaton and an 89-state lower bound are withdrawn;
- the winners are tied to the proved formula.

The reviewer's checks: the formula matches simulation for every `n ≤ 3000`;
`E` matches SS on all 8,360 lazy states of length ≤ 16; no full SS play for
`n ≤ 1500` has two duplicates at once.
