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
equality `S_SS(G_k) = S_SS(G_k − 1)` is proved in §4 from the representation.

## 4. Split Smallest: exact length and regularity (proved)

Write `S(n)` for the SS split count. Its Hankel matrices over Zeckendorf
words of lengths 6, 7 and 8 have rank 6. Separately, a 9-dimensional linear
representation over the blocks `0` and `10` (a trailing `1` is read by a
separate output vector) was fitted on prefixes of length ≤ 10 and suffixes of
length ≤ 8. It was not minimised, so its dimension is an upper bound, not the
rank. It reproduces `S(n)` for every `n ≤ 120,000`
(`evidence/ss_large_range.json`). It is proved exact below ("Regularity"),
so the SS length `n − Z(n) + S(n)` is Fibonacci-regular, since `Z(n)` is.

The winner is the parity of the length. The representation has entries with
denominator 2, so it cannot simply be reduced mod 2. A finite parity automaton
would need a separate argument (an integer representation, or the exact
formula below). The Fatou-property argument after the regularity proof below
supplies one; its size is not computed.

**The block law.** `S(F_k + m) = S(F_k) + S(m) + D_{k mod 2}(m)` for `k ≥ 4`
and `m < F_{k−1}`. Proved below from the representation.

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

**Regularity (proved, computer-assisted).** The 9-dimensional representation
is exact for every `n`. So `S_SS`, and the SS length, are Fibonacci-regular.

*Lemma (the stop is the lazy representation).* Write `y = w* a`, the
stopping word followed by the leftover-ones digit, as a word over
`F_1 = 1, F_2 = 2, …` with `F_1` rightmost. Then `y` is the lazy Fibonacci
representation of `n`: the unique 0/1 word with leading 1 and no two
consecutive `0`s whose value is `n`.

*Proof.*
- **Value.** `y` has value `val(w*) + a = n`.
- **`w*` is lazy.** This is the stopping lemma.
- **No `00` at the end.** It remains to see that `w*` ends in `1` whenever
  `a = 0`. The phase stops only after a step with `r ≤ 1`.
  - The steps ending in `0` are the `r = 1` steps, `x01 → x10` and
    `x1001 → x1010`.
  - Such a step uses two `1`s and gets one back, from the split at index 2.
  - The number of `1`s was at least 2 before the step and is at most 1 after
    it. So it is exactly 1, and `a = 1`.
- **Empty word.** For `n = 1`, `w*` is empty and `y = 1`. ∎

So `S_SS(n) = S_lazy(lazy(n))`, where `S_lazy(y) = T(y⁻) + E'(y)`:

- `y⁻` is `y` without its last letter;
- `T(u) = Σ_{w ∈ 𝓛, w < u} tr₁(w)`;
- `E'(y)` reads the runs of `1`s of `y` from the right, with carry `γ = 0`
  at first. A run of length `k` contributes `⌊(k + γ − 1)²/4⌋`, and then
  `γ ← [k + γ ≥ 2]`.

This is the end-phase formula with the leftover `F_1` treated as part of the
last run. When `w*` ends in `1` and `a = 1`, a run of length `k + 1` with carry
0 contributes what a run of length `k` with carry 1 does. When `w*` ends in `0`
and `a = 1`, the lone `F_1` is a run of length 1 that contributes 0 and leaves
the carry 0.

The proof is a chain of exact constructions
(`verification/reference/ss_regularity.py`):

1. **Rational series on lazy words.** Each piece is a weighted automaton with
   rational weights.
   - `W(w) = tr₁(w)·[w ∈ 𝓛]`: a 4-state automaton for `𝓛`, with a linear
     counter for trailing `1`s.
   - `T`: three modes. *Follow* tracks `u`. *Branch* lets a smaller same-length
     word put `0` where `u` has `1`. *Free* sums over all continuations.
     Shorter words are covered by skipping a nonempty prefix and then running
     free.
   - `T(y⁻)`: one extra state that records `T` of the prefix before the last
     letter.
   - `E'`: read from the right and then transposed. It has finite control (gap
     with carry 0 or 1, run with `m = 1`, run with `m ≥ 2`) and linear counters
     `(1, m, m², [m even])`. The run sum `⌊(m − 1)²/4⌋ = (m² − 2m + 1 − [m even])/4`
     is linear in them.
   - Leading zeros are made inert.
2. **Zeckendorf to lazy.** `Rel` is a finite automaton on aligned digit pairs
   `(x, y)`. Here `x` is a Zeckendorf word and `y` is a lazy word padded with
   leading zeros. `lazy(n)` is never longer than `Zeck(n)`: the lazy words of
   length `l` have values exactly `[F_{l+1} − 1, F_{l+2} − 2]`, and these
   intervals partition the positive integers. That partition also gives
   uniqueness of lazy representations.
   - Its state `(a, b)` records the value difference of the prefixes read:
     `e = a F_{j+1} + b F_j`, with `j` digits still to read.
   - A digit pair moves it to `(a + b + x − y, a)`.
   - It accepts when `a + b = 0` at the end.
   - **Sound:** whatever it accepts has equal values. This holds by
     construction and is replayed on all pairs of length ≤ 10.
   - **Complete:** its domain contains every Zeckendorf word. This is decided
     by subset construction.
   - With uniqueness of lazy representations, `Rel` accepts exactly the pairs
     `(Zeck(n), lazy(n))`.
   - `Rel` is deterministic on digit pairs. So each accepted pair has exactly
     one accepting path, and the composition below counts it once.
   - After trimming it has 9 states, all with `(a, b) ∈ {(0,0), (1,0), (0,1)}`,
     and a larger bound gives the same automaton.
3. **Composition.** `SX(x) = Σ_y [Rel(x, y)] S_lazy(y)` is a 252-dimensional
   representation on Zeckendorf words with `SX(Zeck(n)) = S_SS(n)`.
4. **Equivalence.** The difference between `SX` and the 9-dimensional
   representation (as a letter-level automaton) is identically zero. This is
   decided exactly by the reachable-subspace test, whose reachable space has
   dimension 36.

**Consequences.**

- **The block law.** It holds for all `k ≥ 2` and `m < F_{k−1}`. In the
  representation it says that
  `x₀ C₁₀ C₀^{g−1}(C₀² − I)` annihilates `V(m) − C₀^{|m|} f_E` for all
  `g ≥ 1` and all Zeckendorf words `m`. That is finite linear algebra
  (gate `BLOCK_LAW`).
- **The closed form at Fibonacci numbers.**
  `S(G_k) = S(G_k − 1) = G_{k+1} − (2k² + 8k + 15 + (−1)^k)/8` holds for all
  `k ≥ 2`. Both sides are linear recurrence sequences in `k`.
  - **At `G_k`:** the representation side has order at most 9 (powers of
    `C₀`) and the closed form has order 6, so the total is at most 15.
  - **At `G_k − 1`:** the word is `(10)^p` or `(10)^p 1`, which interleaves two
    sequences of powers of `C₁₀`. That gives order at most 18, so the total is
    at most 24.

  Agreement on `k = 2, …, 40` is therefore a proof. (The actual Hankel rank of
  both sequences is 6.)
- **The winner.** The SS winner is the parity of
  `L_SS(n) = n − Z(n) + S_SS(n)`.
  - The letter-level series (`SX`, or the 9-dimensional representation read
    letter by letter) is integer-valued on all of `{0,1}*`: it is 0 off the
    Zeckendorf words.
  - By the Fatou property of `ℤ`, it is therefore ℤ-rational
    (Berstel–Reutenauer, *Noncommutative Rational Series*, Ch. 7).
  - Reducing a ℤ-representation mod 2 gives a finite automaton for
    `S_SS(n) mod 2`.
  - `n mod 2` and `Z(n) mod 2` are Fibonacci-automatic too (standard).

  So the winner is computed by a finite automaton on Zeckendorf words. Its size
  is not computed here.

What this rests on:

- the written exact formula and the lazy-stop lemma;
- the correctness of the constructions, each replayed against direct
  definitions (gates `COMPONENT_*`, `LAZY_IS_STOP`, `REL_*`,
  `SX_MATCHES_GAME`).

The equivalence, block-law and closed-form steps are exact rational
computations.

## 5. Combine Smallest: the length constant (proved, written)

**Theorem.** `L_CS(n) = c·n + O(log² n)`, where

`c = 1/2 + Σ_{j ≥ 1} (1/F_{2j})(1 − 1/F_{2j+2}) = Σ_{k ≥ 1} 1/f_{2k−1} − 1/φ = 1.2064811686570297199…`

Here `F` is the game indexing (`F_1 = 1, F_2 = 2`) and `f` is the standard
Fibonacci sequence (`f_1 = f_2 = 1`, so `F_k = f_{k+1}`). This proves Li et
al.'s Conjecture 1.4 (CS length linear in `n`, constant `≈ 1.206`) and
identifies the constant. The sum `Σ 1/f_{2k−1}` is transcendental
(Duverney, Nishioka, Nishioka and Shiokawa 1997, as recorded in OEIS
A153387), so `c` is transcendental.

By §1, `L = n − Z(n) + S` with `S` the number of splits, and `Z(n) = O(log n)`.
So it suffices to count splits.

Notation: a configuration is *normal* on an index range if it has no
duplicate and no two consecutive pieces there. The normal configurations on
indices `≤ s` are exactly the Zeckendorf representations of `0, …, F_{s+1} − 1`
(with `F_0 = 1`), so there are `F_{s+1}` of them.

### 5.1 The counter lemma

The *counter* `Q_s` holds a normal configuration on indices `≤ s`. A *feed*
adds one piece at index `s`; then CS runs, and any piece reaching index
`s + 1` is removed at once (a *carry*).

*Lemma (one feed).* For `s ≥ 3`, write the top of the state as
`(c_s, c_{s−1})`. One feed acts as follows.

- **A, top `(0, 0)`:** the new piece stays at `s`. No moves, no carry.
- **B, top `(1, 0)`:** CS splits at `s`. That makes a carry at `s + 1` and
  feeds the sub-counter `Q_{s−2}` (indices `≤ s − 2`) at `s − 2`. The
  sub-counter's carry, if any, stays at `s − 1`. Moves: `1 +` the
  sub-counter's moves; splits likewise.
- **C, top `(0, 1)`:** CS adds `(s − 1, s)` into `s + 1`: one move, one
  carry.

After every feed the state is normal on `≤ s`. There is at most one carry per
feed, and a carry always leaves `c_s = 0`. Moreover, every move of the feed
after its carry stays at indices `≤ s − 1`, and index `s` stays empty until
the next feed.

*Proof.* Induction on `s`. The bases are direct:

- `Q_1` is a ones-add every second feed;
- `Q_2`, in the coordinates `(c_2, c_1)`, goes `(0,0) → (1,0)` with no move,
  then `(1,0) → (0,1)` by a split at 2 (carry at 3, `F_1` returned), then
  `(0,1) → (0,0)` by the add `(1, 2)` (carry at 3).

For `s ≥ 3`, take each case in turn.

- **A.** The new piece has no neighbour and no twin, so there is no move.
- **B.** `c_{s−1} = 0` and the rest is normal, so there is no add. The
  smallest duplicate is at `s`, and its split sends one piece to `s + 1` and
  one to `s − 2`. By induction the sub-counter then normalises inside
  `≤ s − 2` and emits at most one piece at `s − 1`. That piece meets nothing.
  `c_s = 0` after the split. By the induction hypothesis (the last sentence of
  the lemma, applied to `Q_{s−2}`), the sub-counter's moves after its carry
  stay at indices `≤ s − 3`, and its index `s − 2` stays empty. So the piece
  at `s − 1` has no neighbour and no twin for the rest of the feed. All moves
  after the carry at `s + 1` are the sub-counter's, at indices `≤ s − 2`.
- **C.** `c_{s−1} = 1` and normality give `c_{s−2} = 0` and `c_s = 0`. So
  after the feed `(s − 1, s)` is the only consecutive pair, and there is no
  duplicate. The add is the only move.

In B and C the carry is made by a split or an add that empties index `s`. ∎

*Lemma (cycle).* From the empty state, `F_{s+1}` feeds of `Q_s` make
`F_{s+1} − 1` moves, `F_s − 1` of them splits, and `F_s` carries. They visit
every normal state once and return to empty.

*Proof.* Induction on `s`; the bases `s = 1, 2` are the cycles above. For
`s ≥ 3`, run the sub-counter through one full cycle: `D = F_{s−1}` feeds and
`E = F_{s−2}` carries. Each sub-feed costs two feeds of `Q_s` (A then B). Each
sub-carry costs one more (C). So the feeds number `2D + E = F_{s+1}` and the
carries `D + E = F_s`. The moves number `D + E + (F_{s−1} − 1) = F_{s+1} − 1`.
The splits number `D + (F_{s−2} − 1) = F_s − 1`. Values are conserved, so the
state after `k` feeds has value `k F_s mod F_{s+1}`. These values are distinct
for `0 ≤ k < F_{s+1}`, since `gcd(F_s, F_{s+1}) = 1`. ∎

*Rates.* Start from any normal state and make `k` feeds. Then:

- carries `= k F_s / F_{s+1} + θ`, with `|θ| < 1` (the value of a normal
  state lies in `[0, F_{s+1})`);
- splits `= k (F_s − 1)/F_{s+1} + O(s)`, with a constant independent of `s`.

For the second, let `D` be the number of B-feeds among the `k`. The A-feeds
number `D + O(1)` and the C-feeds number `D F_{s−2}/F_{s−1} + O(1)`. So
`D = k F_{s−1}/F_{s+1} + O(1)`. Then `splits_s(k) = D + splits_{s−2}(D)`, and
induction adds `O(1)` per level of `s`. The `O(s)` is the true order: the
worst split error over all start states grows linearly in `s` (about 6.7 at
`s = 14`, per the independent review).

### 5.2 Rounds

Fix an even level `P ≥ 2`. A configuration is in *level form* if:

- it has `p` pieces at `P` (the pile);
- it is normal on `≤ P − 2`;
- indices `P − 1`, `P + 1` and `P + 3` are empty;
- it has `q` pieces at `P + 2` (the output);
- nothing lies above `P + 2`.

*Lemma (round).* In level form with `p ≥ 5`, CS performs a *round* and returns
to level form. A round consists of these moves (a multiset, not a time order):

- a split at `P`, giving `F_{P+1}` and one feed of the counter `Q_{P−2}`;
- the counter's normalisation;
- the add `(P − 1, P) → P + 1` if the counter carried;
- one add `(P, P + 1) → P + 2` per piece that reaches `P + 1`.

The order varies. In case B the first `(P, P + 1)` add comes before the
counter's split, and `(P − 1, P)` comes after the sub-counter's adds but before
its splits. The counts do not depend on the order.

The round makes `2 + 2·[carry] +` (counter moves) moves, of which
`1 +` (counter splits) are splits. It uses `3 + 2·[carry]` pile pieces and adds
`1 + [carry]` output pieces.

*Proof.* In level form there is no add, and the smallest duplicate is the
pile. After the split, CS takes:

- counter adds before pile-region adds (smaller indices);
- pile-region adds before counter splits (adds first).

The counter's moves are the same as in isolation: by the one-feed lemma its
carry at `P − 1` meets only the pile. `(P + 1, P + 2)` is never chosen, because
`(P, P + 1)` is smaller and the pile keeps at least one piece until the last
`(P, P + 1)` add. That add needs `p − 4 ≥ 1` in the worst case (a carry, 5
pieces used), which is `p ≥ 5`; with `p = 5` and a carry the pile ends empty.
Nothing reaches `P + 3`.

For `P = 2` the split returns its `F_1` directly. The `F_1` is the carry, and
`(1, 2) → 3` absorbs it. This is the formula with a trivial counter: every feed
carries and makes no moves. ∎

### 5.3 Tails

*Lemma (tail).* Suppose a level-form state has `p ≤ 4` and `q ≥ 6`. Then
within at most 5 moves outside the counter (counting the split at `P`), plus at
most one counter feed, CS
reaches a split at `P + 2`. At that point the configuration is in level form
for `P + 2`, with at most 2 pieces at `P + 4`.

*Proof.*

- **`p ≤ 1`.** The state is already in level form for `P + 2`. It is normal on
  `≤ P`, because `c_{P−1} = 0`.
- **`p ∈ {2, 3, 4}`.** After the split, the counter's top state decides the
  order (A: no carry; B: carry made by a counter split, after the pile adds;
  C: carry made by a counter add, before them):

| `p` | top | moves after the split, outside the counter | end |
|---|---|---|---|
| 2 | any | `(P+1,P+2)`, `(P+2,P+3)`; a carry stays at `P − 1` | 1 at `P + 4` |
| 3 | A | `(P,P+1)` | nothing above |
| 3 | B | `(P,P+1)`; then the carry stays at `P − 1` | nothing above |
| 3 | C | `(P−1,P)`, then `(P+1,P+2)` twice, then `(P+2,P+3)` twice | 2 at `P + 4`; needs `q ≥ 6` |
| 4 | A | `(P,P+1)`, leaving `p = 1` | nothing above |
| 4 | B | `(P,P+1)`, `(P−1,P)`, `(P+1,P+2)`, `(P+2,P+3)` | 1 at `P + 4` |
| 4 | C | `(P−1,P)`, `(P,P+1)`, `(P+1,P+2)`, `(P+2,P+3)` | 1 at `P + 4` |

In each row the order is CS's: smallest pair first, and adds before splits.
The output keeps at least 2 pieces. Only indices `P − 1, …, P + 4` and one
counter feed are involved, so the table does not depend on `P`. For `P = 2` the
trivial counter acts as top C (the split's `F_1` is the carry).

The bound `q ≥ 6` is sharp only for row 3C. The review found the smallest
working `q` to be 4 for row 2, 3 for rows 4B and 4C, 2 for `p ≤ 1`, and 1 for
rows 3A, 3B and 4A.

The gate `TAIL_CASES` replays every case under CS for even `P ≤ 14`, every
counter state, `p ≤ 6` and `6 ≤ q ≤ 9`. ∎

A level-form state for `P + 2` with up to 2 pieces at `P + 4` still behaves as
in the round lemma: those pieces are output. The full game starts in level form
for `P = 2`, as follows:

- `⌊n/2⌋` ones-adds;
- if `n` is odd, the adds `(1, 2)` and `(2, 3)`.

These are all merges. The gate `LEVEL_START` checks the level form at every
level with a pile of at least 5, for every `n ≤ 3000`.

### 5.4 Assembly

At the start of level `P`, conservation of value gives `n = p_P F_P + v + w`,
with `v < F_{P−1}` (the normal part) and `w ≤ 2 F_{P+2}` (output). So
`p_P = n/F_P + O(1)`.

Let level `P` make `r` rounds. They use `3r + 2E(r) = p_P − O(1)` pile pieces,
where `E(r) = r F_{P−2}/F_{P−1} + O(1)` counts the counter's carries. Since
`3F_{P−1} + 2F_{P−2} = F_{P+2}`, this gives `r = p_P F_{P−1}/F_{P+2} + O(1)`.
The splits at level `P` are then

`r + splits_{P−2}(r) + O(P) = r (F_P − 1)/F_{P−1} + O(P) = n (F_P − 1)/(F_P F_{P+2}) + O(P)`.

The rounds leave `q ≈ n/F_{P+2}` output pieces. So every level with
`n/F_{P+2}` above a fixed constant ends with `q ≥ 6`, and the tail lemma hands
over to level `P + 2` in level form.

Let `P*` be the first level where this fails. Then `F_{P*} ≥ n/C`, and only
`O(log n)` pieces remain, all at indices `O(log n)`.

*Budget lemma.* From any configuration of `m` pieces at indices `≤ I`, every
remaining play has at most `Z(V) + m(I + 3)` moves, where `V` is the value.

*Proof.* The identity of §2 holds between any two configurations:
`L = Σ_end c − Σ_start c − Σ_adds (j − 2) ≤ Σ_end c − Σ_start c`. Write
`c_i = F_{i+2} − i − 2`, and use `|F_{i+2} − φ² F_i| ≤ 1` (gate
`BUDGET_ERROR`). Then `Σ_end c ≤ φ²V + Z(V)` and
`Σ_start c ≥ φ²V − m − m(I + 2)`. ∎

So the levels from `P*` on cost `O(log² n)` moves. Summing the levels below
`P*`:

`S = n Σ_{P even ≥ 2} (F_P − 1)/(F_P F_{P+2}) + O(log² n)`.

The tail of the series beyond `P*` is `O(n/F_{P*}) = O(1)`. Finally,
`1 + Σ (F_P − 1)/(F_P F_{P+2})` equals `c`, by telescoping
`Σ (1/F_P − 1/F_{P+2}) = 1/F_2 = 1/2`. ∎

### 5.5 The closed form

`Σ_{j≥1} 1/F_{2j} = Σ_{k≥1} 1/f_{2k−1} − 1`. For the other sum, use
`1/(f_a f_{a+2}) = 1/(f_a f_{a+1}) − 1/(f_{a+1} f_{a+2})` and
`Σ_{b=1}^{N} (−1)^{b+1}/(f_b f_{b+1}) = f_N/f_{N+1} → 1/φ`. These give
`Σ_{j≥1} 1/(F_{2j}F_{2j+2}) = 1/φ − 1/2`. Hence
`c = Σ 1/f_{2k−1} − 1/φ`. The gate `CONSTANT` checks the three forms of `c`
to 45 digits.

### 5.6 What is and is not proved

- **Proved (written):**
  - the counter lemma and its cycle;
  - the round and tail lemmas;
  - the asymptotic `L_CS(n) = c n + O(log² n)`;
  - the closed form of `c`.
- **Exact computation.** Every step of §5.2–§5.3 is exact, not just
  asymptotic. So the lemmas give an exact algorithm for `L_CS(n)`
  (`verification/reference/cs_exact.py`):
  - the rounds of a level come from a binary search on carry counts;
  - the counter's splits come from floor sums;
  - the last `O(log n)` pieces are simulated directly.

  It takes `O(log³ n)` arithmetic operations. It matches direct simulation for
  every `n ≤ 30,000` and at single `n` up to `4·10⁹`. It also decides the CS
  winner (the parity) for any `n`.
- **Observed, not proved:** `L_CS(n) − c n` is negative and grows like
  `−κ log_φ n` with `κ ≈ 0.42`. It lies in `[−16.4, −1.2]` for `n ≤ 30,000`
  and is `−60.7` at `n = 10³⁰` and `−122.5` at `n = 10⁶⁰`
  (`evidence/cs_deviation_growth.json`). Roughly:
  - `−Z(n)` contributes about `−log_φ n/(φ² + 1)`;
  - the level errors average about `−0.28` per level.

  So the deviation appears unbounded. Only `O(log² n)` is proved.
- **Hankel ranks.** The CS split count has full Hankel rank 13, 21 and 34 at
  the tested lengths. This is evidence that CS is not Fibonacci-regular of
  small rank; it is not a proof, and nothing here decides regularity.

## 6. Winners

- **CL and SL:** the length is `n − Z(n)`, so Player 1 wins exactly when
  `n − Z(n)` is odd.
- **SS:** Player 1 wins when `L_SS(n)` from the exact formula of §4 is odd. For `n ≤ 60`
  the winners are `212112221111211121121222212212121122212212111112212211122221`
  (digit = winning player).
- **CS:** by direct simulation only; §5 fixes the length to within `O(log² n)`, not its parity.

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

A second independent review (fresh agent, own simulators) checked §5. It found
the Combine Smallest theorem proved, with no error or counterexample. It
checked:

- the one-feed lemma for `s ≤ 16`;
- the round and tail lemmas in place for even `P ≤ 18`, `q ≤ 11`, with up to 2
  extra output pieces;
- the level form for `n ≤ 30,000` and samples to `10⁹`;
- the budget lemma on 3,000 random configurations.

Its fixes are applied:

- the `Q_2` base case was in the wrong coordinate order;
- case C cited the wrong reason;
- the one-feed lemma's invariant ("moves after the carry stay below `s`") is
  now stated;
- the round's moves are a multiset, not a time order;
- the tail move bound is 5, not 7, and `P = 2` is covered;
- the unused moves-rate line is dropped.

A third independent review (fresh agent, own simulator, own lazy-representation
code, random words up to length 80, the opposite-direction equivalence test)
found the SS regularity proof correct, given the §4 lemmas. It found no logical
gap. Its wording fixes are applied:

- the order bound at `G_k − 1` is 24, not 15;
- `Rel` is deterministic;
- why `lazy(n)` is never longer than `Zeck(n)`;
- which series the Fatou argument applies to;
- the block law holds for every `k ≥ 2`.
