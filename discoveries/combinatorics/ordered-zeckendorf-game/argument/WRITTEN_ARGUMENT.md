# The Long Game Strategy of the ordered Zeckendorf game: written argument

Indexing: `F_1 = 1, F_2 = 2, F_{k+1} = F_k + F_{k−1}`. Let `φ` be the golden
ratio and `κ = φ/√5 = (5 + √5)/10 = 0.7236…`.

**Theorem.** The Long Game Strategy (LGS) of Bortnovskyi et al. has length

`L_LGS(n) = n²/2 − κ n log_φ n + O(n)`.

So the maximal game length satisfies `M(n) ≥ n²/2 − κ n log_φ n − O(n)`. This
improves the constant 1 of their Theorem 1.10 to `κ`. If their Conjecture 1.7
holds (LGS is longest), the limit of the ratio they plot in Remark 3.1 and
Figure 5, `(n²/2 − M(n))/(n log_φ n)`, is exactly `κ`. They read it as "bigger
than 0.4 and much lower than 1". The ratio converges only like
`κ − 4.17/log_φ n`: it is 0.44 at `n = 10³` and 0.63 at `n = 2·10⁹`, which
explains their reading. `κ` is the density of `1`s in lazy Fibonacci
representations.

## 1. The count model

Under LGS all switches come first. So before every other move the list is
weakly increasing. A switch swaps an adjacent descent and removes exactly one
inversion, and a weakly increasing list has none. So after a non-switch move,
LGS makes exactly as many switches as the move created inversions, in any
order:

`L = Σ_{non-switch moves} (1 + inversions created)`.

On a weakly increasing list with counts `c_i`, the LGS moves and their costs
(inversions created) are as follows.

- **Ones** (`c_1 ≥ 2`): the two leftmost ones become `F_2`, which passes the
  remaining ones. Cost `c_1 − 2`.
- **Split from the right:** the rightmost adjacent equal pair is the last two
  copies of the largest `i ≥ 2` with `c_i ≥ 2`.
  - For `i ≥ 3` it becomes `(F_{i−2}, F_{i+1})`. `F_{i−2}` passes the other
    copies of `i` and all copies of `i − 1`, and `F_{i+1}` passes nothing.
    Cost `c_{i−1} + c_i − 2`.
  - For `i = 2` it becomes `(F_1, F_3)`. Cost `c_2 − 2`.
- **Merge from the left:** the smallest `i` with `c_i, c_{i+1} > 0`. The new
  `F_{i+2}` passes the other copies of `i + 1`. Cost `c_{i+1} − 1`.

So LGS is a deterministic process on counts:

1. ones if `c_1 ≥ 2`;
2. otherwise split the largest duplicate;
3. otherwise merge the smallest consecutive pair.

Each move is charged `1 +` its cost. The gate `COUNT_MODEL` checks this against
direct list simulation for `n ≤ 40`.

## 2. Phases

Write `m = ⌊n/2⌋` and `r = n − 2m`.

**Phase 1.** The first `m` moves are ones. They create
`(n − 2) + (n − 4) + … = m(n − m − 1)` inversions, so phase 1 has length
`m(n − m)`. It leaves `c_1 = r`, `c_2 = m`.

**Pile phase.** This phase runs from the end of phase 1 until the first moment
at which `c_2 ≤ 1`. In it there is always a
duplicate, so there is no merge. Call a *rest moment* one at which the next
move is a split at index 2: then `c_1 ≤ 1` and there is no duplicate above
index 2. Read the pieces at indices `≥ 3` as a binary word `w`, with index 3
rightmost. Let `𝓛` be the counter language: binary words with no `00`, except
one final `00` followed only by `1`s.

*Step lemma.* Suppose that at a rest moment `w ∈ 𝓛` and `c_2 ≥ 2`, and the
pile phase does not end during the step.
Then by the next rest moment the word is the successor of `w` in `𝓛`
(increasing binary order). In between:

- there are exactly `1 + [w ends in 1]` *expensive* splits (at index 2 or 3);
- there are `tr₁(w)` splits at indices `≥ 3`;
- there is at most one ones-move.

The splits at indices `≥ 4` cost 0, a split at 3 costs `c_2`, and the ones-move
costs 0.

*Proof.*

- **The step starts with a split at 2.** It sends `F_1` down and `F_3` up,
  adding 1 at position 0 of `w`. If `c_1` becomes 2, a ones-move (cost 0)
  happens; it touches only indices 1 and 2.
- **The upper part is the SS counter.** Position `p` of the word is index
  `p + 3`.
  - A duplicate at position 0 (index 3) splits into position 1 and an `F_1`.
  - A duplicate at position 1 (index 4) splits into position 2 and an `F_2`,
    which goes to the pile.
  - A duplicate at position `p ≥ 2` splits into positions `p + 1` and `p − 2`.

  This is exactly the word process of the Split Smallest counting lemma
  (deterministic-zeckendorf-games, `argument/WRITTEN_ARGUMENT.md` §4), with the
  same carry pattern. The pieces leaving at positions 0 and 1 leave the word in
  both cases.
- **Only one upper duplicate at a time.** That proof shows that every deposit
  at `p − 2` lands on a cell the carry has already cleared. So there is only
  one upper duplicate at a time, and LGS's "largest first" picks the same split
  as "smallest first". The pile duplicate at index 2 is never chosen while an
  upper duplicate exists. So the word moves to the `𝓛`-successor and makes
  `tr₁(w)` upper splits.
- **Expensive splits.** Position 0 holds a duplicate exactly when `w` ends in
  `1`. That gives one split at index 3 with `c_3 = 2`, costing `c_2 + 2 − 2`.
- **Free splits.** A split at position `p ≥ 1` has `c_j = 2`, and its lower
  neighbour (position `p − 1`) has been cleared. So it costs `0 + 2 − 2 = 0`.
- **Ones.** A ones-move has `c_1 = 2` exactly and costs 0. ∎

The first rest word is the empty word.

**Tail.** Once `c_2 ≤ 1`, at most `O(log n)` pieces remain, all at indices
`O(log n)`. The non-switch moves are Zeckendorf-game moves. The budget lemma
(deterministic-zeckendorf-games §5.4) bounds their number by `O(log² n)`. Each
creates at most `O(log n)` inversions. So the tail costs `O(log³ n)`.

## 3. Exact accounting

Number the expensive splits of the pile phase `k = 1, …, E`.

- Let `U` be the value at indices `≥ 3` and `P` the number of pieces there.
  The quantity `Q = U − 2P` starts at 0 and changes as follows:
  - a split at 2 gives `ΔU = 3`, `ΔP = 1`, so `ΔQ = 1`;
  - a split at 3 gives `ΔU = −1`, `ΔP = −1`, so `ΔQ = 1`;
  - a split at 4 gives `ΔU = −2`, `ΔP = −1`, so `ΔQ = 0`;
  - a split at `≥ 5`, or a ones-move, gives `ΔQ = 0`.

  So just before split `k`, `Q = k − 1` (gate `INVARIANT_Q`).
- Conservation of value, `2c_2 + c_1 + U = n`, then gives
  `c_2^{(k)} = (n − c_1^{(k)} − (k − 1) − 2P^{(k)})/2`.

By the step lemma the pile phase costs `moves + Σ_k c_2^{(k)} − 2s_2`, where
`s_2` counts splits at 2 and `moves` counts the non-switch moves of the pile
phase. Substitute this, the phase-1 length `m(n − m)`, `E = n − e`,
`n²/2 − m(n − m) = n²/4 + r²/4` and `Σ_k (n − k + 1)/2 = (n² + n − e − e²)/4`.
This gives

`n²/2 − L = Σ_k P^{(k)} + R`, where
`R = −n/4 + r²/4 + (e + e²)/4 + Σ_k c_1^{(k)}/2 + 2s_2 − moves − tail`.

This is an exact identity. The gate `EXACT_IDENTITY` checks this closed form of
`R` for every `n ≤ 600`, both parities. Every term of `R` is `O(n)`:

- `c_1 ≤ 1`;
- `s_2 ≤ E ≤ n`;
- `moves` is at most the number of non-switch moves of the whole game. That is
  a Zeckendorf-game play, so it is at most `Σ_{Zeck(n)} c_i ≤ φ² n` by the
  identity of deterministic-zeckendorf-games §2 (about `2.1 n` is observed);
- the tail is `O(log³ n)`;
- `e = O(log n)`. At the end of the pile phase `U ≥ n − 3`, so
  `E = U − 2P + O(1) = n − O(log n)`.

So `n²/2 − L = Σ_k P^{(k)} + O(n)`.

## 4. The density

In the step from rest word `w`:

- at its split at 2, `P = ds(w)` (the digit sum of `w`);
- at its split at 3 (if any), `P = ds(w) + 1`.

Hence

`Σ_k P^{(k)} = Σ_{w ∈ 𝓛, w < W} (1 + [w ends in 1]) ds(w) + O(n)`,

with `W` the last rest word. The weights `1 + [w ends in 1]` sum to `E`.

*Density lemma.* Over the `𝓛`-words of length `ℓ`, with weight
`1 + [ends in 1]`, the weighted sum of `ds` is `κ ℓ` times the total weight,
plus at most twice the total weight.

*Proof.* A transfer-matrix computation over the automaton of `𝓛`.

- Lazy words (no `00`) are the complements of golden-mean words (no `11`). The
  frequency of `1`s there is `1/(φ² + 1)`, so here it is `1 − 1/(φ² + 1) = κ`.
- The weight depends only on the last digit.
- The tail words `x1001^j` add `O(1 + j)` per word, with `j` geometrically
  distributed.

The gate `DENSITY` checks the bound exactly for `ℓ ≤ 60`; the transfer matrix
gives it for all `ℓ`. ∎

**The partial last length.** The rest words of the last length `ℓ*` form a
prefix of that length class in increasing order. Such a prefix is a disjoint
union of cylinders: the words `u0s`, one for each `1` of the boundary word,
with `u` its prefix before that `1`.

- The suffix `s` ranges over the completions allowed by `𝓛` after `u0`. That
  is a free `𝓛`-type suffix, or, if `u0` already ends in `00` or contains the
  `00`, the forced forms `01^j` or `1^j`.
- A cylinder fixed at depth `i` has weight `O(φ^{ℓ*−i})`.
- On its free part the density lemma applies; the fixed digits and the forced
  forms err by `O(i)` per word.

Summed over `i`, the weighted digit sum of the prefix is `κ ℓ*` times its
weight, plus `O(Σ_i i φ^{ℓ*−i}) = O(φ^{ℓ*}) = O(n)`. The error is `O(n)`, not
`O(weight)`: relative to a small prefix's weight it can grow with `ℓ*`. `O(n)`
is all that is needed.

**Summing over lengths.** The weight on length `ℓ` decays like `φ^{ℓ−ℓ*}`
below `ℓ*`, and `ℓ* = log_φ n + O(1)` (`𝓛`-words of length `ℓ` have values
`≍ F_{ℓ+3}`). Hence

`Σ_w (1 + [ends in 1]) ds(w) = κ ℓ* E + O(E) = κ n log_φ n + O(n)`. ∎

## 5. What is and is not proved

- **Proved (written):**
  - the count model;
  - the step lemma, which transfers the reviewed SS counting lemma;
  - the exact identity;
  - `L_LGS(n) = n²/2 − κ n log_φ n + O(n)`.
- **Observed:** `(n²/2 − L)/n − κ log_φ n` lies in `[−4.21, −4.06]` for
  `n = 10³, …, 10⁹` (`evidence/lgs_large.json`). The `O(n)` term is about
  `−4.17 n`.
- **Exhaustive check:** the maximal game length `M(n)` equals the LGS length
  for every `n ≤ 16` (exhaustive search over ordered states). This is consistent
  with Conjecture 1.7, not a proof of it.
- **Not claimed:**
  - that LGS is longest (Conjecture 1.7);
  - any improvement of the upper bound `M(n) ≤ n²/2 − (1/32) n log_φ n`;
  - who wins.

## 6. Review

An independent review (fresh agent, own list simulator and count model, `n` up
to `2·10⁹`) found the theorem proved, with fixable gaps. All are fixed here:

- the closed form of `R` was off by `m`, because the phase-1 length `m(n − m)`
  had been taken for its switch count;
- the partial-last-length error is `O(n)`, not `O(weight)`;
- the forced suffixes are now named;
- the pile phase is defined precisely;
- the bound on `moves` is justified;
- the Remark 3.1 claim is stated as a limit;
- the paper's authors are Bortnovskyi, Lucas, Miller, Vraneško, Watson and
  White.

The identity gate now tests the closed form.
