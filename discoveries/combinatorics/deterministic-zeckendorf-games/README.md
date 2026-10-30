# Deterministic Zeckendorf games: Split Smallest exactly, Combine Smallest's constant

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
exact length was known for SS or CS. Their Conjecture 1.4 says the CS length is
linear in `n` with constant `≈ 1.206`.

## What this dossier finds

- **The add moves decide the length (written; holds for every game).** A
  potential argument gives the length of any play exactly:
  `L = Σ_{i ∈ Zeck(n)} c_i − Σ_{add-consecutive moves} (j − 2)`.
  Here `j` is the index produced, and `c_1 = 0, c_2 = 1, c_3 = 3,
  c_{i+1} = 2c_i − c_{i−2} + 1`. The `c_i` are the longest-game weights of
  Cusenza et al., who note an exact formula in terms of move counts.
  The number of merging moves is always `n − Z(n)`, so the length is
  `n − Z(n) + #splits`.
- **Split Smallest is Fibonacci-regular (proved, computer-assisted).**
  The SS split count has a 9-dimensional linear representation, read over the
  Zeckendorf blocks `0` and `10`. It was fitted on words of length ≤ 18 and is
  exact for every `n`.

  How it is proved (`ss_regularity.py`):
  - the exact formula below depends on `n` only through its lazy Fibonacci
    representation;
  - that dependence is a rational series, built explicitly;
  - a 9-state automaton converts Zeckendorf words to lazy ones;
  - the composed 252-dimensional representation is decided equal to the
    9-dimensional one, by exact linear algebra.

  So the SS length is Fibonacci-regular, and the SS winner (its parity) is
  computed by a finite automaton. An independent review found the proof
  correct given the written lemmas; its wording fixes are applied. Player 1 wins SS for about half of all `n`
  (50.02% up to 120,000).
- **Closed form at Fibonacci numbers.** In the shifted sequence `G_k = F_{k+1}`
  (`G_0 = 1, G_1 = 2`):
  `S_SS(G_k) = S_SS(G_k − 1) = G_{k+1} − (2k² + 8k + 15 + (−1)^k)/8` for all
  `k ≥ 2`. This is proved from the representation: both sides are linear
  recurrences in `k` of total order at most 24, and they agree for
  `k = 2, …, 40`.
- **The exact length of Split Smallest (proved, written).**
  `L_SS(n) = n − Z(n) + Σ_{w ∈ 𝓛, w < w*} tr₁(w) + E(w*, n − val(w*))`.
  Here:
  - `𝓛` is the counter language below, in increasing order;
  - `w*` is its first word of value at least `n − 1`;
  - `tr₁` counts trailing `1`s;
  - `E` is an explicit end-phase count, a sum over the blocks of `w*` of
    `⌊(k − 1 + γ)²/4⌋` with a carry bit `γ`.

  This matches simulation for every `n ≤ 120,000`. The winner is its parity.
  An independent review found the proof correct up to fixable gaps (a run-lemma
  hypothesis, one misstated case); those are fixed in version 0.3.0.
- **The counting phase is the lazy Fibonacci counter (proved, written).**
  While two `1`s remain, each SS step adds them into a `2` and normalises by
  splits. The step moves the upper word to the next word, in increasing order,
  of the binary words with no `00` except one final `00 1…1`: the lazy
  Fibonacci representations plus a transient tail. It makes as many splits as
  the previous word has trailing `1`s.
- **SS length is `φ² n − O(log² n)` (proved).** This follows from the exact
  formula and the length identity. It proves both directions of the SS part
  of Li et al.'s Conjecture 1.4; Cusenza et al. argue only the upper bound.
- **A block law (proved).** `S_SS(F_k + m) − S_SS(F_k) − S_SS(m)` depends
  only on `m` and the parity of `k`, for `k ≥ 2` and `m < F_{k−1}`. This is proved by
  finite linear algebra on the representation.
- **The Combine Smallest constant (proved, written).**
  `L_CS(n) = c·n + O(log² n)`, with
  `c = Σ_{k≥1} 1/f_{2k−1} − 1/φ = 1.2064811686570297…`. Here `f` is the
  standard Fibonacci sequence, so `c` is the sum of reciprocal odd-indexed
  Fibonacci numbers minus `1/φ`. That sum is transcendental (Duverney et al.
  1997), so `c` is too. This proves Li et al.'s Conjecture 1.4 and names the
  constant.

  The mechanism:
  - CS moves a pile up two indices at a time;
  - below the pile, a counter absorbs one piece per split;
  - the counter is a self-similar Fibonacci counter: `F_{s+1}` feeds cost
    exactly `F_{s+1} − 1` moves and return it to empty.

  The same lemmas give an exact algorithm (`cs_exact.py`) for `L_CS(n)`, and
  so for the CS winner. It takes `O(log³ n)` arithmetic operations and matches
  simulation everywhere tested. An independent review found the proof correct;
  its small fixes are applied.

  Observed, not proved: `L_CS(n) − c·n` is negative and grows like
  `−0.42 log_φ n`. It is `−22` at `10⁹` and `−123` at `10⁶⁰`.
- **Combine Smallest is not low-rank.** Its Hankel matrices over Zeckendorf
  words have full rank (13, 21, 34 at word lengths 6, 7, 8). That is evidence,
  not proof, that CS is not Fibonacci-regular of small rank.
- **Winners of CL and SL.** Player 1 wins exactly when `n − Z(n)` is odd. This
  is immediate from the known length.

## What is not established

- A machine-checked (proof-assistant) version of the written proofs. The SS
  regularity proof is computer-assisted: exact computation on top of the
  written exact formula.
- The size of the minimal SS parity automaton.
- A closed form for the CS length or winner beyond the polylog algorithm; a proof that `L_CS(n) − c·n` is `Θ(log n)`.
- Novelty beyond the cited papers. See [`review/PRIOR_ART.md`](review/PRIOR_ART.md).

## Smallest decisive tests

- A gap in the counting-phase or end-phase lemma; see `argument/WRITTEN_ARGUMENT.md` §4.
- An `n` where SS's split count differs from the representation. That would
  refute the exact formula or the regularity construction.
- A gap in the CS counter, round or tail lemma; see §5. A counter state where
  one feed does not follow the A/B/C rule would break it.

## Reproduction

```text
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/zeckendorf_games.py 3000
cc -O2 -o deterministic_games discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/deterministic_games.c
./deterministic_games 120000 S > ss.txt
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/check_large.py ss.txt
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/ss_regularity.py
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/cs_constant.py 3000
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/cs_exact.py 3000
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/cs_deviation_growth.py
./deterministic_games 30000 C > cs.txt
cc -O2 -o cs_single discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/cs_single.c
./cs_single 1000 10000 100000 1000000 10000000 100000000 1000000000 4000000000 > cs_single.txt
python -B discoveries/combinatorics/deterministic-zeckendorf-games/verification/reference/check_cs_large.py cs.txt cs_single.txt
```

## Repository map

- `argument/`: the written argument.
- `verification/reference/`: the game simulator, the gated checks, the SS
  representation (`ss_linrep.json`), and the optional C simulator.
- `evidence/`: check outputs.
- `review/`: prior art.
- `revisions/`: revision history.
