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

  What remains is:
  - rule 1: `(i − 2)/3 + β`;
  - rule 2(b): `(i − 1)/3 + β`;
  - rule 3(g): exactly 1;
  - rule 4(e): `4/3`.

  Each is at least 1 for `i ≥ J` (gate `TAIL_ANALYTIC`).

*Rule 2(a)* (`q_1, q_5 → q_2, q_4`, only when no other move is possible) is
used at most once in a game (Miller–Newlon, Lemma 2.2). It raises `Φ` by
`Δ = u_1 + u_5 − u_2 − u_4 ≈ 1.94`.

*Start and end.* At the start, `Φ = −n·u_1 = 0`. Every weight satisfies
`u_i ≤ α q_i`: this is checked for `i < J`, and holds for `i ≥ J` since
`β ≥ 0`. So at the end `Φ ≥ −α Σ q = −α n`.

*Count.* With `L` moves,
`−αn ≤ Φ_end ≤ 0 − (L − 1) + Δ`. Hence `L ≤ αn + 1 + Δ < (23/10)n + 2.95`. ∎

## How sharp

- **Exhaustive maxima.** The longest games for every `n ≤ 90` were computed
  exhaustively (`fq_longest_exhaustive.cpp`, about 11 million states).
  - The longest game first reaches `2n` at `n = 78`.
  - The largest ratio found is `2.022`, at `n = 89`
    (`evidence/fq_longest_n_le_90.json`).
  - So the maximum does exceed `2n`, even though random games stay below it.
- **The potential method.** The best constant this method can give, a
  potential with a linear tail `α q_i − c·i − β`, is about `2.2899`. That is
  the limit of a linear program over the rule constraints, solved
  numerically (`fq_potential_lp.py`, which needs scipy). It is infeasible with
  slack at `α = 2.29` but feasible at `α = 2.3`.
- **Comparison with the maxima.** The per-`n` linear-program bound stays
  within 12 moves of the exhaustive maximum for `50 ≤ n ≤ 90`. That suggests,
  without proving it, that the true constant is close to `2.29`.

## Not claimed

- That `2.3` is optimal, or the exact asymptotic constant of the longest game.
- Who wins.
- Anything about random games.
