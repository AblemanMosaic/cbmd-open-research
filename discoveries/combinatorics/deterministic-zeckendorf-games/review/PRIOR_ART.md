# Prior art

- P. Baird-Smith, A. Epstein, K. Flint, S. J. Miller, *The Zeckendorf game*
  (arXiv 1809.04881): the rules, termination at the Zeckendorf decomposition,
  and a non-constructive proof that Player 2 wins for `n > 2`.
- R. Li, X. Li, S. J. Miller et al., *Deterministic Zeckendorf games*,
  Fibonacci Quart. 58 (2020) (arXiv 2006.16457):
  - defines CL, SL, CS and SS;
  - Theorem 1.3: CL and SL have length `n − Z(n)`;
  - Conjecture 1.4: SS is linear in `n` with constant `φ²`, and CS with
    constant `≈ 1.206`;
  - asks how long each game takes and who wins, as a function of `n`.
- A. Cusenza et al., *Bounds on Zeckendorf games*, Fibonacci Quart. 60 (2022)
  (arXiv 2009.09510):
  - Theorem 1.2: the longest game splits and adds `1`s whenever possible (SS);
  - Theorem 1.3: the sharp bound `Σ c_i`-type in terms of move counts;
  - Theorem 1.4: only-split-and-ones-add play exists exactly when
    `n = F_k − 1`;
  - they note the bound could be tightened by counting combining moves.
- Later work, such as the ordered Zeckendorf game (arXiv 2508.20222), cites
  the deterministic games without determining SS or CS lengths.

The length identity of §2 is a rewriting of Cusenza et al.'s exact formula.
What is proposed as new:

- the Fibonacci-regularity of SS, with an explicit representation;
- the closed form at `F_k`;
- the block law;
- the Hankel-rank evidence separating CS from SS;
- the resulting winner descriptions.

None of these is proved here except the `F_k − 1` closed form, which rests on
Cusenza et al.'s theorems. Not a novelty determination.
