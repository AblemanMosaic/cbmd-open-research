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

Since 0.3.0 the exact SS length is proved here (written), and since 0.4.0 the
CS constant: `L_CS(n) = c n + O(log² n)` with `c = Σ 1/f_{2k−1} − 1/φ`.

- The sum of reciprocal odd-indexed Fibonacci numbers is OEIS A153387
  (`1.8245151574…`). Its theta-function form goes back to Landau (1899). Its
  transcendence is due to D. Duverney, Ke. Nishioka, Ku. Nishioka and
  I. Shiokawa, Proc. Japan Acad. 73A (1997) 140–142.
- Searches (October 2026) found no later paper that determines the CS
  constant or proves Conjecture 1.4. The random-game work (arXiv 2210.11038)
  and the ordered and reversed variants (arXiv 2508.20222, 2309.12748) do not
  address it.

Since 0.5.0, SS regularity, the block law and the `G_k` closed form are proved
as well (computer-assisted, on top of the written exact formula). The rational
series and transducer constructions are standard (Berstel–Reutenauer;
Frougny on Fibonacci normalisation); their use here is specific to this game.
Not a novelty determination.

Cusenza et al. write that their sharp upper bound settles the `φ²` constant of
Conjecture 1.4 for SS. Their argument gives only the upper bound. The matching
lower bound `L_SS ≥ φ² n − O(log² n)` follows from the exact formula here (§4).
