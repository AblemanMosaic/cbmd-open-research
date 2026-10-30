# Deterministic Zeckendorf games: Split Smallest is Fibonacci-regular

> **Standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`, `CONJECTURE`

Permanent claim ID: `CBMD-COMB-DET-ZECK-001`

## The question

The two-player Zeckendorf game starts from `n` copies of `F_1 = 1`. The
indexing is `F_1 = 1, F_2 = 2, F_3 = 3, …`. A move is one of:

- adding two `1`s into a `2`;
- adding two consecutive Fibonacci numbers into the next one;
- splitting a duplicate: `2F_2 = F_1 + F_3`, or `2F_i = F_{i−2} + F_{i+1}`.

The game ends at the Zeckendorf decomposition of `n`.

Li, Li, Miller et al. (*Deterministic Zeckendorf games*, Fibonacci Quart. 58
(2020)) define four deterministic games by fixing a priority among the moves:
Combine Largest (CL), Split Largest (SL), Combine Smallest (CS) and Split
Smallest (SS). They ask: *"For each of the four deterministic games, how long
do they take and who wins as a function of n?"* For CL and SL they prove the
length is `n − Z(n)`. SS is known to realise the longest possible game. No
exact length was known for SS or CS.

## What this dossier finds

- **The add moves decide the length (written; holds for every game).** A
  potential argument gives the length of any play exactly:
  `L = Σ_{i ∈ Zeck(n)} c_i − Σ_{add-consecutive moves} (j − 2)`.
  Here `j` is the index produced, and `c_1 = 0, c_2 = 1, c_3 = 3,
  c_{i+1} = 2c_i − c_{i−2} + 1`. The `c_i` are the longest-game weights of
  Cusenza et al., who note an exact formula in terms of move counts.
  The number of merging moves is always `n − Z(n)`, so the length is
  `n − Z(n) + #splits`.
- **Split Smallest is Fibonacci-regular (conjecture, exhaustively checked).**
  The SS split count has a 9-dimensional linear representation, read over the
  Zeckendorf blocks `0` and `10`. It was fitted on words of length ≤ 18 and
  reproduces the split count exactly for every `n ≤ 120,000`. So the SS length,
  and therefore the SS winner (the parity of the length), are given by an
  explicit finite linear representation. Player 1 wins SS for about half of all
  `n` (50.02% up to 120,000).
- **Closed form at Fibonacci numbers.** With `F_0 = 1, F_1 = 2`:
  `S_SS(F_k) = S_SS(F_k − 1) = F_{k+1} − (2k² + 8k + 15 + (−1)^k)/8`. At
  `F_k − 1` this follows from Cusenza et al.'s theorems plus the identity
  above (written argument). At `F_k` it is checked up to `k = 24`.
- **The counting phase is the lazy Fibonacci counter (proved, written).**
  While two `1`s remain, each SS step adds them into a `2` and normalises by
  splits. The step moves the upper word to the next word, in increasing order,
  of the binary words with no `00` except one final `00 1…1`: the lazy
  Fibonacci representations plus a transient tail. It makes as many splits as
  the previous word has trailing `1`s.
- **A block law.** `S_SS(F_k + m) − S_SS(F_k) − S_SS(m)` depends only on `m`
  and the parity of `k`, for `k ≥ 4` and `m < F_{k−1}`. Checked to 120,000.
- **Combine Smallest is different.** Its Hankel matrices over Zeckendorf words
  have full rank (13, 21, 34 at word lengths 6, 7, 8). That is evidence, not
  proof, that CS is not Fibonacci-regular of small rank. Its length ratio
  converges to `1.20648…`, the constant conjectured by Li et al.
- **Winners of CL and SL.** Player 1 wins exactly when `n − Z(n)` is odd. This
  is immediate from the known length.

## What is not established

- A proof that SS is Fibonacci-regular, or of the block law and the
  closed form at `F_k`. The counting phase is proved; the end phase and the
  assembly are not.
- Anything exact about CS beyond the evidence above.
- Novelty beyond the cited papers. See [`review/PRIOR_ART.md`](review/PRIOR_ART.md).

## Smallest decisive tests

- An `n` where SS's split count differs from the representation.
- A proof of the block law, which would make the regularity a theorem.

## Reproduction

```text
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/zeckendorf_games.py 3000
cc -O2 -o deterministic_games discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/deterministic_games.c
./deterministic_games 120000 S > ss.txt
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/check_large.py ss.txt
```

## Repository map

- `argument/`: the written argument.
- `verification/reference/`: the game simulator, the gated checks, the SS
  representation (`ss_linrep.json`), and the optional C simulator.
- `evidence/`: check outputs.
- `review/`: prior art.
- `revisions/`: revision history.
