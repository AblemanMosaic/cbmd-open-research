# Capacity preservation in Petri nets: a characterization at one input place and coNP-completeness at two

> **Pipeline stage:** `REVIEW_READY`
>
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `SOURCE_BOUND_COMPILED`,
> `EXACT_MODEL_VERIFIED`

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

## One region is now proved (revision 0.2.0)

Everything above is census. One part of the map is now a theorem.

Call a net **increasing** when every transition strictly increases the token
count at some place, and **inert** at `C` when no transition can ever fire
inside the box.

> For an increasing net, `PRESERVES(N, C)` holds **exactly when** the net is
> inert at `C`.

The whole proof is one marking. Take `m = C`. Firing any transition from it
would push its strictly-increasing place over capacity, so `C` is capacity-dead;
and any transition whose inputs fit inside the capacities is ordinarily enabled
there. So an increasing net is either frozen or broken, with nothing in between,
and raising the capacities does not help because the witness is rebuilt from
whatever the capacities are.

This says something about the predecessor rather than only about Petri nets.
A chip-firing transition increases a place — *unless* the receiver is the
absorbing sink, which carries no capacity. The sink is the only thing keeping
chip-firing outside this hypothesis.

Compiled in Lean 4.35.0 with no proof escape and without `Classical.choice`,
including the modelling step that admissible markings and capacity-reachable
markings are the same set. Corroborated over 37,197 nets in the class with zero
disagreements, of which 25,586 are non-inert; the hypothesis is load-bearing,
since outside the class the conclusion is wrong on 39,464 nets. See
[`revisions/0.2.0-allfull-obstruction.md`](revisions/0.2.0-allfull-obstruction.md).

## The draining regime, characterized (revision 0.3.0)

Revision 0.2.0 stops at transitions that **drain** — consume without producing —
because they keep the all-full marking alive. For unit-weight flow nets, where
each transition takes one token from a place and either moves it elsewhere or
discards it, the answer is a filled-set condition. Call a set `S` of places an
**obstruction** when

1. every member has positive capacity,
2. no drain takes from a member,
3. every mover out of a member lands in `S` or in a zero-capacity place,
4. some mover takes from a member.

> `PRESERVES(N, C)` holds **exactly when** no obstruction exists.

Fill `S` to capacity and empty everything else: every transition from `S` is a
mover, and it is blocked either by a full member or by a zero-capacity
receiver. Conversely the places a failing marking occupies form an obstruction.

This is the live-set obstruction of the predecessor widened twice — a
transition may discard its token, and a zero-capacity receiver may do the
blocking in place of a full one. Both directions compile, with no finiteness.
Exact over 133,887 systems with zero unsound and zero incomplete; each of the
four conditions is load-bearing, and the greatest-fixpoint decision procedure
is checked against the proved existential form rather than assumed to match it.
See [`revisions/0.3.0-flow-characterization.md`](revisions/0.3.0-flow-characterization.md).

## The dichotomy (revision 0.4.0)

Version 0.1.0 left this open: *whether some other local capacity condition
repairs the multi-input case*, with the explicit non-claim that no
impossibility was being asserted. It is now answered, and more sharply than
"some other condition might work".

| transitions have | status |
|---|---|
| at most one input place | characterized above; decidable by a greatest fixpoint in polynomial time |
| two input places | **coNP-complete**, at unit weights and capacities in `{0,1}` |

Membership is easy: the complement — *does a bad marking exist* — is in NP,
since an admissible marking is polynomial-sized even with binary capacities
and both halves of "bad" are checked in `O(PT)`.

Hardness uses the two ways a transition can fail to be capacity enabled. With
unit weights and capacities in `{0,1}`, *"some place holds less than the
transition consumes"* reads as a negative literal and costs an input place,
while *"firing would overflow some place"* reads as a positive literal and
costs none. One transition per clause, inputs on its negative literals and
outputs on its positive ones, is blocked exactly when the clause is satisfied.
A guard construction keeps every transition fed while holding the negative
literals per clause to two, so every transition has one or two input places.

So the structural boundary this dossier found by census and the boundary of
tractability are the same boundary — which the mechanism already suggested:
a multi-input transition is enabled by a conjunction, and conjunctions are what
turn a reachability question into a satisfiability one.

This is a **written argument**, not a compiled theorem; formalizing it needs a
model of computation, which is a different artifact from the Lean in this
dossier. What is machine-checked is the reduction: 240 instances, 240
agreements, zero disagreements, 171 satisfiable against 69 unsatisfiable, every
transition carrying one or two input places. See
[`revisions/0.4.0-hardness-dichotomy.md`](revisions/0.4.0-hardness-dichotomy.md).

## The mechanism

The descent argument certifies one place at a time: this receiver is full, so it
is above a threshold, so something downstream can fire. Enabledness of a
multi-input transition is a **conjunction** over places, and per-place capacity
bookkeeping cannot discharge a conjunction. The minimal witness has two places:
at marking `(1,1)` the enabled transition is blocked, the receiving place is
indeed above its consumer's threshold on that place, and the consumer is still
not enabled because its other input is short.

## What remains unresolved

- A formal proof of the complexity statement. coNP-completeness is argued in
  prose with a machine-checked reduction; it is not compiled.
- Whether the polynomial one-input case extends to weighted arcs.
- Novelty. The nearest named notions are implicit places and non-blockingness of
  bounded nets; neither is this statement. See [`review/README.md`](review/README.md).
- Weighted flow and multi-input transitions. The obstruction condition of
  revision 0.3.0 is proved for unit-weight, single-input, single-output
  transitions only.
- Apart from the all-full obstruction, everything here is a finite census over
  stated boxes.

## Smallest decisive tests

- A chip-firing-shaped net satisfying the conditions with a capacity-dead,
  ordinarily enabled marking.
- A local capacity condition, checkable per place, that is sound over the
  multi-input boxes where the usable-transition refinement fails.

## Reproduction

```text
python -B discoveries/concurrency/capacity-preservation-boundary/verification/run_checks.py
```

With the pinned toolchain available:

```text
python -B discoveries/concurrency/capacity-preservation-boundary/verification/lean/replay.py --build
```
