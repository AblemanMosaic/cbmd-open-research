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
`w(j) − w(j−1) − w(j−2) = −(c_j − c_{j−1} − c_{j−2}) = −(j − 1)`, by induction
on `j`.

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
no add moves there. The Zeckendorf decomposition of `F_k − 1` is
`F_{k−1} + F_{k−3} + …`. Substituting `c_i = F_{i+2} − i − 2` and summing the alternating indices (Fibonacci and arithmetic sums) gives the closed form

`S_SS(F_k − 1) = F_{k+1} − (2k² + 8k + 15 + (−1)^k)/8`, with `F_0 = 1, F_1 = 2`.

The gate `SS_FIBONACCI_closed_form` checks this. The equality
`S_SS(F_k) = S_SS(F_k − 1)` is checked, not proved.

## 4. Regularity of Split Smallest (conjecture)

Write `S(n)` for the SS split count. Its Hankel matrix over Zeckendorf words
has rank 6 at word lengths 6, 7 and 8. A 9-dimensional linear representation
over the blocks `0` and `10` (a trailing `1` is read by a separate output
vector) was fitted on prefixes of length ≤ 10 and suffixes of length ≤ 8. It
reproduces `S(n)` for every `n ≤ 120,000`
(`evidence/ss_large_range.json`). By §1 the SS length is `n − Z(n) + S(n)`;
`Z(n)` is regular, so the length is too.

The winner is the parity of the length. So it is computed by the same
representation reduced mod 2, which a finite automaton on Zeckendorf words can
read. A naive search found at least 89 states, so this is not a simple rule.

**The block law.** `S(F_k + m) = S(F_k) + S(m) + D_{k mod 2}(m)` for `k ≥ 4`
and `m < F_{k−1}`. This is the shape a structural proof would take.

**What a proof needs.** The state of the SS process always has at most one
duplicate among the pieces at indices ≥ 2, and no count above 2 (observed for
`n < 400`). So the process acts as a Fibonacci counter: it absorbs a `2` and
normalises by splits. The open part is to show that its carry counts compose
along Zeckendorf blocks as the block law states.

## 5. Combine Smallest

The CS split count has Hankel rank 13, 21 and 34: full rank at every tested
length. It is not Fibonacci-regular of small rank in the tested window. Its
length ratio is `1.206474` at `n = 10^6` and `1.206480` at `n = 9,227,465`,
consistent with Li et al.'s conjectured `≈ 1.20647`.

## 6. Winners

- **CL and SL:** the length is `n − Z(n)`, so Player 1 wins exactly when
  `n − Z(n)` is odd.
- **SS:** Player 1 wins when the representation's length is odd. For `n ≤ 60`
  the winners are `212112221111211121121222212212121122212212111112212211122221`
  (digit = winning player).
- **CS:** by direct simulation only.
