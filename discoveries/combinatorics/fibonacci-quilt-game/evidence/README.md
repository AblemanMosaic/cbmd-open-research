# Evidence

| File | Contents |
|---|---|
| `fq_bound.json` | Exact checks: rules preserve value; the potential drops by at least 1 on every rule instance with indices `≤ 200`; the closed-form tail; `u_i ≤ α q_i`; the exhaustive longest game for `n ≤ 40` within the bound; a control. |
| `fq_longest_n_le_90.json` | Exhaustive longest games for `n ≤ 90` (C++ search), the SHA-256 of the output, the first `n` with a game of length at least `2n`, and the largest ratio. |
| (tool) `fq_lemma22_check.cpp` | Exhaustive check that rule 2(a) is used at most once from every position where it is the only move (other indices ≤ 40), under three readings of rule 3(f). |
| `fq_long_strategy.json` | A priority strategy and its exact game lengths at `n = 90, 10³, …, 10⁶` (`2.2782n` at `10⁶`). |
