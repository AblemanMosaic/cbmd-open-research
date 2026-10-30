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

In Murata's vocabulary, *capacity enabled* and *ordinarily enabled* are the
**strict** and **weak** transition rules for finite-capacity nets, so the
question reads: does the strict rule admit a dead marking that the weak rule
does not? The obstruction below is a **trap** in the original net — dually a
siphon in the complemented net — with one extra branch for zero-capacity
places. Both are standard objects; see [`review/PRIOR_ART.md`](review/PRIOR_ART.md)
for what is and is not known, including why the coNP-completeness here is
**not** a sharpening of the PSPACE-completeness of deadlock for 1-safe nets:
that problem quantifies over *reachable* markings, and this one does not.

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

## One input place is the whole story (revision 0.6.0)

The dichotomy is stated in **input** places, and the hardness construction uses
only that ordinary enabledness is a conjunction over inputs. Outputs never
enter it — so the polynomial side should not be confined to nets that feed one
place, and it is not.

With one input place, "capacity-dead" is one clause per transition with a
single negative literal, so the capacity-dead admissible markings are **closed
under pointwise maximum**. There is therefore a greatest one, `M`, and since
ordinary enabledness is monotone,

> `PRESERVES(N, C)` holds **exactly when** `M` is ordinarily dead.

`M` is computed by lowering from the capacities: whenever a transition is
capacity-enabled, drop its input place to one below its own weight. Each
lowering is justified, and the procedure emits that justification as a
certificate which a checker re-derives — so "greatest" is discharged rather
than assumed. Exact over 31,905 systems with arbitrary outputs and weights,
zero unsound and zero incomplete, all certificates replaying. See
[`revisions/0.6.0-single-input.md`](revisions/0.6.0-single-input.md).

This supersedes the *procedure* of revision 0.5.0 — one downward fixpoint in
place of one upward fixpoint per transition, over a wider class — while its
characterization below stands as the statement of what a failure looks like.

Revision 0.7.0 compiles the last prose step. Each lowering strictly drops the
total token count, so the iteration halts and a certified greatest marking
always exists; `preserves_decided_by_lowering` states the whole single-input
case in one theorem. Compiling it exposed a hypothesis that had been implicit
— that each transition really does consume from the place named as its input
— which the structure had never required. See
[`revisions/0.7.0-termination.md`](revisions/0.7.0-termination.md).

## Weights: the obstruction carries levels (revision 0.5.0)

The unit-weight proof above does not survive weights, and not for a technical
reason. Its converse rests on raising every occupied place to its capacity;
with weights, raising `m(a)` from 1 to 5 can make a transition that takes 3
from `a` ordinarily enabled when it was not, and nothing need block it. So the
obstruction has to carry **levels** rather than membership.

A level function `ℓ` is an obstruction when `ℓ ≤ C`, every drain has
`ℓ(src) < w`, every mover with `w ≤ ℓ(src)` has `C(dst) < ℓ(dst) + v`, and
some transition has `w ≤ ℓ(src)`. Preservation holds exactly when none exists,
and the unit-weight condition is the case `ℓ ∈ {0,1}`.

Clause 3 read as an implication — `w ≤ ℓ(src) ⟹ ℓ(dst) ≥ C(dst) − v + 1` — is
monotone, which gives the decision procedure: seed at each transition in turn,
close, test. Completeness is the compiled part, and it is derived rather than
assumed: an inductive `Forced` predicate records the lower bounds any failing
marking must satisfy, so a closure whose every level is forced is below every
failing marking and testing it misses nothing. Exact over 102,268 weighted
systems, zero unsound and zero incomplete, with all 48,775 accepted closures
carrying a derivation that a separate checker validates. See
[`revisions/0.5.0-weighted-flow.md`](revisions/0.5.0-weighted-flow.md).

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

This was first a **written argument**, with the reduction machine-checked by
census: 240 instances, 240 agreements, zero disagreements, 171 satisfiable
against 69 unsatisfiable, every transition carrying one or two input places. See
[`revisions/0.4.0-hardness-dichotomy.md`](revisions/0.4.0-hardness-dichotomy.md).

Since revision 0.9.0 the reduction itself is **compiled**:
`preserves_iff_unsatisfiable` states that the net built from the guarded form
of any CNF preserves exactly when the CNF is unsatisfiable, and
`guard_neg_count` with the input-place lemmas gives one or two input places per
transition. A bridge check confirms the compiled net is the census's net. The
formalization surfaced an unstated hypothesis — no clause may contain an atom
with both signs — which the guarded encoding provably satisfies. What remains
prose is only the complexity-class wrapper: membership in coNP and the
polynomial running time of the reduction. See
[`revisions/0.9.0-reduction-compiled.md`](revisions/0.9.0-reduction-compiled.md).

## Free choice does not help (revision 0.10.0)

Free-choice nets are where Petri-net problems usually become tractable. Not
this one: the hardness survives in **strict free-choice** nets with unit
weights and **every capacity equal to 1**. Places `x_i`, `x̄_i`, `g`; a
transition `x_i, x̄_i → ∅` per variable, and transitions `g → (literal places)`
per clause. Only `g` is shared, and it is the sole input of everything that
reads it. The compiled theorem is `fc_preserves_iff_unsatisfiable`; a census of
315 formulas agrees exactly, with every net checked to be free choice.

The proof also predicted that one gadget is idle except on the empty CNF, and
the census confirmed it. This is parallel to, not a corollary of, Cheng,
Esparza and Palsberg's NP-completeness of *reachable* deadlock in free-choice
nets. See [`revisions/0.10.0-free-choice.md`](revisions/0.10.0-free-choice.md).

## Marked graphs are polynomial (revision 0.11.0)

On the other side of the free-choice line: in a **marked graph** — at most one
consumer and one producer per place — preservation is polynomial at any
weights and capacities, multi-input transitions included. Each place then
occurs in at most two blocking constraints, and the question becomes an
orientation problem on a graph whose edges are places, decided by counting
edges and vertices per component. This is a written argument with a census of
20,000 nets (zero disagreements, two load-bearing ablations), not a compiled
theorem. *Conflict-free* nets — one consumer, many producers — sit between and
are open. See [`revisions/0.11.0-marked-graphs.md`](revisions/0.11.0-marked-graphs.md).

## Between the regimes (revision 0.8.0)

The coNP-hardness needs **unboundedly many** multi-input transitions. With a
fixed number `k` of them, preservation is polynomial: each is blocked by one of
finitely many unit literals — a short input or an overflowing place — and
choosing one per such transition leaves every branch max-closed, so the
greatest admissible solution decides it. That is branching on a strong backdoor
to Horn (Nishimura, Ragde and Szeider) and is claimed only as an application.
It completes the picture: polynomial with none, FPT in `k`, coNP-complete when
unbounded. Exact over 145,953 nets with zero unsound and zero incomplete. See
[`revisions/0.8.0-few-multi-input.md`](revisions/0.8.0-few-multi-input.md).

## The mechanism

The descent argument certifies one place at a time: this receiver is full, so it
is above a threshold, so something downstream can fire. Enabledness of a
multi-input transition is a **conjunction** over places, and per-place capacity
bookkeeping cannot discharge a conjunction. The minimal witness has two places:
at marking `(1,1)` the enabled transition is blocked, the receiving place is
indeed above its consumer's threshold on that place, and the consumer is still
not enabled because its other input is short.

## What remains unresolved

- Conflict-free nets (each place has at most one consumer, any number of
  producers): neither the free-choice reduction nor the marked-graph argument
  applies. See revision 0.11.0.
- The marked-graph procedure of revision 0.11.0 is a written argument with a
  census; it is not compiled.

- A formal proof of the complexity-class statement. The reduction's
  correctness and input-place bounds are compiled (revision 0.9.0); membership
  in coNP and the reduction's polynomial running time are argued in prose.
- ~~The construction behind the decision procedure is prose: the induction
  placing the least closure below every failing marking, and the termination of
  the closure iteration, are not compiled.~~ Stale: both were compiled, in
  revisions 0.5.0 (`WFlow.forced_le_of_bad`) and 0.7.0 (termination).
- Novelty. The nearest named notions are implicit places and non-blockingness of
  bounded nets; neither is this statement. See [`review/README.md`](review/README.md).
- ~~Weighted flow and multi-input transitions. The obstruction condition of
  revision 0.3.0 is proved for unit-weight, single-input, single-output
  transitions only.~~ Stale: weights are handled by revision 0.5.0, arbitrary
  outputs by 0.6.0, and multi-input transitions are coNP-complete (0.4.0) and
  fixed-parameter tractable in their number (0.8.0).
- ~~Apart from the all-full obstruction, everything here is a finite census over
  stated boxes.~~ Stale since revision 0.3.0; see the standing table in each
  revision for what is compiled and what is censused.

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
