# The Fibonacci Quilt game: a linear bound on game length

## Setting

Quilt numbers: `q_1, …, q_4 = 1, 2, 3, 4` and `q_i = q_{i−2} + q_{i−3}`
(`i ≥ 5`), so `5, 7, 9, 12, 16, 21, …`. The game of Miller and Newlon
(Fibonacci Quart. 58 (2020); arXiv 1909.01938) starts from `n` copies of `q_1`
and uses their rules 1–5. These combine consecutive terms, terms at distance 3
or 4, or two equal terms, and the game ends at an FQ-legal decomposition.

Rule 3(f) is printed as `q_6, q_6 → q_2, q_8` or `q_3, q_7`. The second option
does not preserve the value (`14 ≠ 12`), so we read it as `q_5, q_7`
(`5 + 9 = 14`). Every other rule preserves the value as printed (gate
`RULES_PRESERVE_VALUE`).

Their open question (Section 3): *"Is there a reasonable upper bound on the
length of a game?"* They add that simulations "have never given a game of
length close to or longer than 2n".

## Theorem

Every Fibonacci Quilt game on `n` has at most `(23/10)·n + 2.95` moves.

## Proof

Let `Φ = −Σ_{pieces} u(index)`, with weights `u` as follows
(`verification/reference/fq_potential.json`):

- for `i < J = 31`, `u_i` is an explicit rational, with `u_1 = 0`;
- for `i ≥ J`, `u_i = α q_i − i/3 − β`, with `α = 23/10` and an explicit
  rational `β ≈ 3.40`.

*Every move except rule 2(a) lowers `Φ` by at least 1.* A move removes pieces
`R` and adds pieces `A`; we need `Σ_A u − Σ_R u ≥ 1`.

- **Small indices.** Every rule instance whose indices are all `≤ 200` is
  checked in exact rational arithmetic (gate `POTENTIAL_EXACT`).
- **Large indices.** An instance with an index above 200 has all its indices
  `≥ 191 ≥ J`, so it lies in the closed-form region. There the `α q_i` terms
  cancel, because the four large-index rules preserve value:
  - `q_{i+3} = q_i + q_{i+1}`;
  - `q_{i+5} = q_i + q_{i+4}`;
  - `2q_i = q_{i−5} + q_{i+2}`;
  - `q_i + q_{i+3} = q_{i−5} + q_{i+4}`.

  These identities hold for all `i ≥ 7`. The first is the defining recurrence.
  The second is `q_{m+1} = q_m + q_{m−4}` (`m ≥ 6`, Miller–Newlon Theorem 1.6)
  with `m = i + 4`. The third and fourth follow from the first two: write
  `q_{i+2} = q_i + q_{i−1}`, `q_{i−1} = q_{i−2} + q_{i−6}`, and so on. They are
  also checked for `i ≤ 200`.

  What remains is:
  - rule 1: `(i − 2)/3 + β`;
  - rule 2(b): `(i − 1)/3 + β`;
  - rule 3(g): exactly 1;
  - rule 4(e): `4/3`.

  Each is at least 1 for `i ≥ J` (gate `TAIL_ANALYTIC`).

*Rule 2(a)* (`q_1, q_5 → q_2, q_4`, only when no other move is possible) is
used at most once in a game (Miller–Newlon, Lemma 2.2). It raises `Φ` by
`Δ = u_1 + u_5 − u_2 − u_4 ≈ 1.94`.

The bound depends on that lemma: no potential of this shape makes 2(a)
decrease. The paper's proof is a sketch, so it was rechecked computationally
(`fq_lemma22_check.cpp`, by the independent reviewer):

- every position in which 2(a) is the only move, with other indices up to 40
  (78,464 positions), was explored exhaustively;
- this was done under three readings of rule 3(f);
- 2(a) is used at most once every time, and from `1^n` for `n ≤ 90`.

*Start and end.* At the start, `Φ = −n·u_1 = 0`. Every weight satisfies
`u_i ≤ α q_i`: this is checked for `i < J`, and holds for `i ≥ J` since
`β ≥ 0`. So at the end `Φ ≥ −α Σ q = −α n`.

*Count.* With `L` moves,
`−αn ≤ Φ_end ≤ 0 − (L − 1) + Δ`. Hence `L ≤ αn + 1 + Δ < (23/10)n + 2.95`. ∎

## How sharp

- **Exhaustive maxima.** The longest games for every `n ≤ 90` were computed
  exhaustively (`fq_longest_exhaustive.cpp`, about 11 million states).
  - The longest game first equals `2n` at `n = 78`, and first exceeds `2n` at
    `n = 86`.
  - The largest ratio found is `2.022`, at `n = 89`
    (`evidence/fq_longest_n_le_90.json`).
  - So the maximum does exceed `2n`. Miller and Newlon's remark that
    simulations never came near `2n` concerned random games, which this
    dossier does not test.
- **The potential method (numerical, not proved).** A floating-point linear
  program over a finite index window (`fq_potential_lp.py`, which needs scipy)
  finds no potential of this shape below `α ≈ 2.2899`. The tail slope was
  fixed at `1/3`; the reviewer found the same value with it free, for windows
  31, 41 and 61. This is not an infeasibility certificate. The LP is
  infeasible with slack at `α = 2.29` and feasible at `α = 2.3`.
- **A long strategy.** A fixed priority strategy, found by local search over
  priority orders of move classes (`fq_strategy.cpp`,
  `evidence/fq_long_strategy.json`), reaches:
  - `2.2318n` at `n = 10³`;
  - `2.2774n` at `n = 10⁵`;
  - `2.278223n` at `n = 10⁶`.

  Each value is an exact simulation of a legal game, so the longest game at
  that `n` is at least that long. Exhaustive maxima for small `n` are lower
  (`2.02n` at `n ≤ 90`) only because small-index effects dominate there.
- **The true constant.** So the longest game at `n = 10⁶` has between
  `2.2782n` and `2.3n + 2.95` moves. Whether the asymptotic constant is the
  potential limit `≈ 2.2899` is open; the strategy's ratio appears to level
  off near `2.2785`.

## Not claimed

- That `2.3` is optimal, or the exact asymptotic constant of the longest game.
- Who wins.
- Anything about random games.

## Review

An independent review (fresh agent) re-typed the rules from the paper and
re-derived the certificate in exact arithmetic for indices up to 400. It
re-ran the exhaustive search with its own code and rule table (11,408,896
states, all values matching), and checked Lemma 2.2 as described above. It
found the theorem sound.

Its fixes are applied:

- the q-identities are now derived for all `i`;
- the potential-method limit is stated as a numerical observation;
- an unsupported "within 12 moves" comparison is removed;
- the `2n` statements are made precise;
- the control gate is strengthened.

Under the narrower reading of rule 3(f), `q_2, q_8` only, only `n = 67`
changes (131 instead of 132).
