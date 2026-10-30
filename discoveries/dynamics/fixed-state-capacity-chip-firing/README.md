# Capacity-blocked chip-firing from a fixed state: strongly NP-hard on a star

> **Standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `SOURCE_BOUND_COMPILED`,
> `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-DYN-FIXED-STATE-001`

## The contrast

[`CBMD-DYN-WEIGHTED-CAPACITY-001`](../weighted-capacity-chip-firing/README.md)
characterizes, over arbitrary digraphs, when capacity-blocked chip-firing
reaches the ordinary normal form from **every** admissible initial state. It
gives a decider proved correct in Lean that runs in polynomial time.

From one **fixed** initial state the same question is **strongly NP-hard**,
already on a star with one receiver.

## Exact claim

*FIXED-GOOD*: given a capacity-blocked chip-firing system (multiplicities,
outdegrees, capacities, an absorbing sink) and an admissible initial state `x`,
is the ordinary normal form of `x` reachable by capacity-legal firings?

Take `k` senders. Sender `i` holds `a_i > 0` chips, has outdegree and capacity
`a_i`, and sends all of them to one receiver `v`. The receiver has outdegree
and capacity `B` and sends everything to the sink. Then:

- the reachable states are exactly the **bin runs**. These are orders of
  firing in which each bundle fits into `v`'s current fill, with the fill
  resetting when it reaches `B` (`reach_iff`);
- bin runs are exactly sequences of **disjoint blocks of total exactly `B`**,
  followed by an open block of total at most `B` (`run_iff_blocks`);
- so when `Σ a_i` is a multiple of `B`, the normal form is reachable **iff the
  bundles partition into groups each of total `B`**
  (`normal_form_reachable_iff_partition`).

That is bin packing with exact fill, which contains 3-PARTITION. 3-PARTITION
is NP-complete in the strong sense (Garey–Johnson), and the transformation
copies its numbers unchanged. So FIXED-GOOD is strongly NP-hard on stars, with
multiplicities and capacities written in unary. On stars it is in NP: a bin run
of at most `2k` steps is a certificate. In general it lies in PSPACE, because
states are bounded by the capacities.

## What is established

- **Compiled** (Lean 4.35.0, Mathlib-free, no `sorry`, axioms within
  `propext, Classical.choice, Quot.sound`): `reach_iff`,
  `all_fired_reachable_iff`, `bad_terminal_reachable_iff`, `run_iff_blocks`,
  `normal_form_reachable_iff_partition`, and (0.2.0) `fill_eq_mod`,
  `stuck_imp_witness`, `safe_of_no_witness`, and (0.3.0) `realise_small`,
  `realise_pair`, `bad_of_small_or_pair_witness`, and (0.4.0) `spec_iff`,
  `dpWitness_iff`, `dpFast_eq`, `safe_of_dpFast`, `safe_2_3_3`, and (0.5.0)
  `stuck_of_oversize`, `bad_of_dpBad`, `classify_safe`, `classify_bad`,
  `bad_2_2_3_3_3`, and (0.6.0) `realise_split`, `bad_of_split`,
  `bad_of_triple`, `bad_of_onebin`, `bad_of_dpBadT`, `classifyT_safe`,
  `classifyT_bad`. They are proved against the
  capacity-blocked chip-firing semantics of the weighted dossier, copied
  verbatim. `verification/semantics_custody.py` checks the copy declaration by
  declaration, with a mutation control.
- **Exact census** (`verification/reference/star_reduction.py`): 1,208 random
  stars. Both decision predicates named by the theorems agree with the weighted
  dossier's exhaustive simulator on every instance:
  - "an exact-bin order exists" against "the normal form is reachable";
  - "some bin run gets stuck" against "a bad terminal state is reachable".
  
  It also checks that the normal form is the all-fired state with `Σ a mod B` at
  the receiver, as the theorems assume.
- **Consistency with the weighted theorem:** every census instance that meets
  the weighted bound `C(v) ≥ d(v) + max a − 1` is good. Hardness lives strictly
  below that bound.
- **Written:** the complexity-class wrapper. It consists of the strong
  NP-hardness of 3-PARTITION (cited), polynomiality of the transformation, NP
  membership on stars, and PSPACE membership in general.

## Getting stuck on the star (0.2.0)

*FIXED-BAD* asks whether firing from `x` can end in a terminal state that is
not ordinarily stable. On the star:

- **Compiled:** when a run stops short of full, the receiver's fill is the
  residue `(Σ_fired a) mod B` (`fill_eq_mod`). So a stuck run hands over a
  **residue witness**: a set `F` of senders, missing at least one, such that
  every sender outside `F` overflows on top of `(Σ_F a) mod B`
  (`stuck_imp_witness`). Its contrapositive is a **safety certificate**: no
  residue witness means no reachable bad ending (`safe_of_no_witness`).
- **Compiled decider (0.4.0):** the witness condition depends only on the pair
  (residue of the fired total, smallest unfired bundle). A table of the pairs
  that occur, built one sender at a time in `O(kB²)` entries, is proved exact
  (`spec_iff`, `dpWitness_iff`). Its array-memoised implementation is proved
  equal to it (`dpFast_eq`). So `dpFast = false` is a **verified safety
  certificate** (`safe_of_dpFast`); for example, the star with bundles
  `2, 3, 3` and `B = 5` is certified in the kernel (`safe_2_3_3`). A sorted
  `O(kB)` variant is a written argument checked by enumeration.
- **Compiled three-way classifier (0.5.0):** `classify` answers `safe`, `bad`
  or `unknown`. `safe` (no witness) and `bad` are both proved correct
  (`classify_safe`, `classify_bad`). `bad` means: a bundle too big ever to fit,
  or a witness with one or two unfired senders, checked in `O(k²)`. In the
  exhaustive range it answers `safe` 3,991 times, `bad` 490,329 times and
  `unknown` 6,141 times (1.2%); every `unknown` instance has a witness, so it
  is bad if the conjecture holds. The kernel certifies `bad_2_2_3_3_3` this
  way. The extended `classifyT` (0.6.0) also checks witnesses with three
  unfired senders. It leaves 531 unknowns in the range, all of which are in
  fact bad.
- **Compiled partial converse (0.3.0, extended 0.6.0):** a residue witness is
  realised by a stuck run in each of these cases:
  - its unfired senders total at most `B` (`realise_small`);
  - its fired part fits in one bin (`bad_of_onebin`);
  - its unfired senders split as `T ⊔ W`, where `T` totals at most `B`, each
    member of `W` overflows on top of `T`, and the members of `W` overflow
    pairwise (`realise_split`).

  The split case covers every witness with at most three unfired senders
  (`bad_of_triple`) and every witness in which no two unfired senders fit
  together. In the exhaustive range (`B ≤ 13`, `k ≤ 8`), every one of the
  496,470 instances with a witness has a witness of one of these shapes. So
  in that range the conjecture follows from the compiled theorems plus a
  finite check of shapes.
- **Conjectured, not proved:** every residue witness is realised by a stuck
  run. Sharper: for a witness of least fired total, firing its set
  largest-fit-first realises it. The evidence is exhaustive: all 500,461 star instances with B ≤ 13 and k ≤ 8, no counterexample. If the conjecture holds,
  "can it end badly?" is pseudo-polynomial on stars while "can it end well?" is
  strongly NP-hard there. The conjecture is specific to one receiver. With two
  receivers an explicit system has a witness but, by exact simulation, no bad
  ending.

## What remains unresolved

- **The residue-witness conjecture** above, in the case not covered: every
  witness leaves unfired senders of total above `B`, with no split, and fires
  a part that needs more than one bin. The smallest such instances found are
  `B = 10` with bundles `2, 4×9` and `B = 15` with `3, 6×8`. Both do get stuck,
  but only by a two-bin run. Proving this case would settle FIXED-BAD and its
  complement FIXED-MUST-GOOD on stars in pseudo-polynomial time. Natural
  extremal proof routes fail in range; see `argument/WRITTEN_ARGUMENT.md` §6.
  FIXED-BAD on general graphs is open.
- The exact complexity of FIXED-GOOD in general: NP-hard, in PSPACE. Whether it
  is in NP on all graphs is open, since firing vectors can be exponential on
  digraphs even with unary multiplicities.
- Whether hardness survives with **unit** multiplicities. The star needs large
  bundles; cycles also create order dependence with unit edges.
- Novelty and external review. See [`review/PRIOR_ART.md`](review/PRIOR_ART.md).

## Smallest decisive tests

- Against the correspondence: a star whose normal form is capacity-reachable
  although its bundles admit no exact-bin partition, or the reverse.
- Against the contrast: a polynomial algorithm for FIXED-GOOD on stars would
  give one for 3-PARTITION.

## Reproduction

```text
python -B discoveries/dynamics/fixed-state-capacity-chip-firing/verification/run_checks.py
python -B discoveries/dynamics/fixed-state-capacity-chip-firing/verification/lean/replay.py --build
```

## Repository map

- `argument/`: the written argument, including the complexity wrapper.
- `verification/lean/`: Lean sources (`Semantics`, `Star`, `Bins`, `Stuck`, `Realise`, `ResidueDecide`, `Split`) and replay driver.
- `verification/reference/`: the star census against exact simulation, the residue-witness check, and two optional C searches (`bin_runs_exhaustive.c`, `one_step_lemma_search.c`).
- `verification/semantics_custody.py`: checks the copied semantics against the weighted dossier.
- `evidence/`: census output, bundled checks and the Lean receipt.
- `review/`: prior-art note.
- `revisions/`: revision history.
