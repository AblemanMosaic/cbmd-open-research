# Where the capacity-preservation characterization transfers, and where it stops

> **Pipeline stage:** `REVIEW_READY`
>
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`

Permanent discovery ID: `CBMD-CON-CAPACITY-PRESERVATION-001`

A boundary study for [`CBMD-DYN-WEIGHTED-CAPACITY-001`](../../dynamics/weighted-capacity-chip-firing/README.md).
That result characterizes when a capacity preserves the terminal states of
chip-firing. Its proof uses almost nothing specific to chip-firing, so this asks
how far it reaches, in Petri nets with place capacities — where a transition may
consume from several places, and the question needs no confluence at all.

## Exact question

**PRESERVES(N, C)**: every capacity-reachable marking that is capacity-dead is
also dead in the uncapacitated net. A capacity-dead but ordinarily enabled
marking is a deadlock the capacity invented.

## What is established

- **It transfers exactly to chip-firing-shaped nets** — one input place per
  transition, distinct across transitions, no transition feeding its own input.
  Zero unsound and zero incomplete over 1,152 and 10,368 systems in two boxes.
  This independently reproduces the chip-firing characterization in a
  differently coded model.
- **Self-feedback costs completeness, not soundness.** Allowing a transition to
  return tokens to the place it drains produced 1,636 incomplete cases and
  **zero** unsound ones. The conditions stay sufficient there.
- **Shared consumption and conjunctive input break it**, with 80 and 48 unsound
  witnesses. These are exactly the two features chip-firing lacks.
- **The natural repair is not enough.** Refining liveness to track which
  transitions can fire at all leaves the conditions unsound over three boxes
  (64, 7,200 and 552 witnesses).

## The mechanism

The descent argument certifies one place at a time: this receiver is full, so it
is above a threshold, so something downstream can fire. Enabledness of a
multi-input transition is a **conjunction** over places, and per-place capacity
bookkeeping cannot discharge a conjunction. The minimal witness has two places:
at marking `(1,1)` the enabled transition is blocked, the receiving place is
indeed above its consumer's threshold on that place, and the consumer is still
not enabled because its other input is short.

## What remains unresolved

- Whether **some** local capacity condition repairs the multi-input case. Only
  the natural one is refuted here, with witnesses; no impossibility is claimed.
- Novelty. The nearest named notions are implicit places and non-blockingness of
  bounded nets; neither is this statement. See [`review/README.md`](review/README.md).
- Everything here is a finite census over stated boxes. No unbounded theorem
  about general Petri nets is established.

## Smallest decisive tests

- A chip-firing-shaped net satisfying the conditions with a capacity-dead,
  ordinarily enabled marking.
- A local capacity condition, checkable per place, that is sound over the
  multi-input boxes where the usable-transition refinement fails.

## Reproduction

```text
python -B discoveries/concurrency/capacity-preservation-boundary/verification/run_checks.py
```
