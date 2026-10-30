# Capacity-blocked chip-firing: sharp weighted bound and a live-set characterization

> **Standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `SOURCE_BOUND_COMPILED`,
> `EXACT_MODEL_VERIFIED`, `INDEPENDENTLY_REPRODUCED`

Permanent claim ID: `CBMD-DYN-WEIGHTED-CAPACITY-001`

This resolves the successor question left open by
[`CBMD-DYN-CAPACITY-FIRING-001`](../finite-capacity-chip-firing/README.md):
whether the candidate bound `C(v) >= d(v) + max_u m(u,v) - 1` suffices for
weighted transfers. It does.

## Exact claim

Let a finite loopless directed multigraph have an absorbing sink, nonsink arcs
pointing strictly forward in a fixed vertex order, and every nonsink vertex
reaching the sink. Let `b(v)` be any upper bound on incoming multiplicity,
`m(u,v) <= b(v)` for all `u`, and assume

```
d(v) + b(v) <= C(v) + 1          (equivalently C(v) >= d(v) + b(v) - 1)
```

Then capacity-blocked firing terminates, and every capacity-terminal state
reachable from an initial state is that state's ordinary (uncapacitated) normal
form. With `b(v) = 1` this is the predecessor's unit-edge theorem.

## What is established

- A Lean 4.35.0 development compiles the weighted overflow lemma, the
  preservation of terminal states, and the full transfer theorem, with no
  `sorry` and observed axioms exactly `[propext, Classical.choice, Quot.sound]`.
  The receipt records the actual `#print axioms` output, not only a manifest.
- Exact enumeration found **no** failure at the bound: 8,364 systems at
  `n <= 3, m <= 3`, and 4,596 at `n <= 4, m <= 2`.
- A separately implemented checker tested the theorem's own conclusion —
  every capacity-terminal state equals the ordinary normal form — over 96,053
  initial states with zero disagreements.
- The bound is **sharp**. Lowering it by one at any receiver of incoming
  multiplicity at least two produces failures: 84 systems in the small box,
  380 at `n <= 4`.

The finite enumeration corroborates the theorem; it does not prove it.

## A distinction the enumeration exposed

Confluence and transfer are **not** the same property here. The smallest
capacity failure at `C(v) = d(v)` is *confluent* — it has exactly one normal
form — but that normal form is not the ordinary one:

```
m(0,1) = 2, one sink arc from 1.  d = (2,1), C = (2,1).
From (2,0): vertex 0 is blocked, vertex 1 is stable, so (2,0) is the unique
capacity-terminal state.  The ordinary normal form is (0,0).
```

A search that looks only for two distinct normal forms cannot see this. The
checks in this dossier therefore gate on the transfer property and report
nonconfluence only as a secondary statistic.

## The ordered hypothesis is necessary (revision 0.2.0)

Cyclic graphs are not merely out of scope; they are impossible. If the arc
relation contains a directed cycle and `C(v) >= d(v)` on it, then filling every
cycle vertex to capacity and emptying the rest gives a capacity-terminal state
that is not ordinarily stable. Each cycle vertex is blocked by its successor,
which is full. Because the witness is built from the capacities themselves, **no
enlargement of capacity restores preservation**. A forward ordering provably
excludes the structure this uses, so the two results partition the model:

| arc relation | status |
|---|---|
| forward-ordered | preservation holds at `d(v) + b(v) <= C(v) + 1`; sharp |
| contains a directed cycle | preservation fails at every capacity with `C(v) >= d(v)` |

Confirmed in all 27,440 tested cyclic graph and capacity pairs, with an
exhaustive state sweep finding no cyclic system that preserves transfer at any
slack from 0 to 4. See [`revisions/0.2.0-cycle-obstruction.md`](revisions/0.2.0-cycle-obstruction.md).

## A characterization over arbitrary digraphs (revision 0.3.0)

Dropping both the ordering and the assumption that every vertex can fire, write
`Live v` for `outdegree v <= capacity v`. A vertex outside the live set is
permanently ordinarily stable, because its chips never exceed its capacity.
Transfer then holds exactly when the live set is

1. **ordered** — its arcs admit a rank, i.e. the live subgraph is acyclic,
2. **bounded** — `outdegree v + mult u v <= capacity v + 1` on live arcs,
3. **closed** — live vertices send only to live vertices.

Condition 3 was not anticipated: a live vertex pointing at a dead one is blocked
forever once the dead receiver fills, while ordinary firing proceeds regardless.

Over **798,025 systems** the three conditions agree with the exact transfer
property in every case — zero unsound, zero incomplete — and each is separately
necessary (dropping them makes the predicate wrong on 63,847 / 4,998 / 393,192
systems respectively).

Sufficiency is proved, and so is the necessity of the bound and of live-closure,
each by an explicit compiled witness. Ordering plus live-closure also provably
exclude every obstruction of this shape. See
[`revisions/0.4.0-necessity.md`](revisions/0.4.0-necessity.md).

Both failures are also now **one** theorem. `filled_set_obstruction`: fill any
set whose live members point back into it, empty the rest, and the state is
capacity-terminal but not ordinarily stable. The cycle and the live-to-dead case
are instances. See [`revisions/0.3.0-characterization.md`](revisions/0.3.0-characterization.md).

## The ordering condition becomes an equivalence (revision 0.5.0)

Condition 1 above carried an unproved step: *no rank function exists* had to be
turned into a concrete obstruction, which is the classical finite-digraph fact
that an acyclic finite relation admits a topological order. That step is now
gone — not proved, but no longer needed.

Replace the rank by well-foundedness of the receiver-chasing relation

```
LiveArc v u   iff   Live u  and  Live v  and  mult u v > 0
```

Then sufficiency holds with **no finiteness at all**
(`wf_terminal_implies_ordinary_stable`), and the old hypotheses are recovered as
an instance (`wellFounded_of_rank`). More to the point, the obstruction can be
built directly out of the hypothesis failing: take membership to be *"not
accessible"*; from an inaccessible vertex there is always an arc to another
inaccessible vertex, and that is exactly the successor map a filled set needs.
A vertex that is not live is accessible for free, so the witness is live with no
extra hypothesis. The two directions give

```lean
wellFounded_iff_no_filled_set :
  WellFounded (LiveArc ..) ↔ (FilledSet .. → False)      -- under live-closure
```

What was still imported was only that a *finite acyclic* live subgraph is well
founded — the statement that lets the census **decide** the hypothesis by cycle
detection. It was not a step inside any theorem, and since revision 0.8.0 it is
compiled as well (`liveArc_wellFounded_iff_acyclic`; see
[`revisions/0.8.0-finite-acyclic.md`](revisions/0.8.0-finite-acyclic.md)).

A content check written not to share machinery with the census — Kahn peeling
for well-foundedness, a greatest-fixpoint kernel for filled sets, direct
simulation of the theorem's own conclusion — agrees over the same 798,025
systems: 0 unsound, 0 incomplete. It also confirms a *prediction*: well-
foundedness failing forces the conclusion to fail, with zero exceptions in
260,172 systems. See
[`revisions/0.5.0-wellfounded-equivalence.md`](revisions/0.5.0-wellfounded-equivalence.md).

## No ordinary hypothesis left (revision 0.10.0)

`weighted_transfer` took the firing function and the ordinary theory as
parameters. `weighted_transfer_concrete` binds firing to the multigraph
update. It proves termination by lexicographic descent, and uniqueness by local
commutation and Newman's lemma. So the weighted theorem now stands on its
structural hypotheses alone. See
[`revisions/0.10.0-concrete-transfer.md`](revisions/0.10.0-concrete-transfer.md).

## One compiled equivalence (revision 0.9.0)

The pieces of the characterization are now assembled:

```lean
terminalStable_iff_acyclic :
  TerminalStable ↔ (live subgraph acyclic) ∧ LiveClosed ∧ LiveBound
```

`TerminalStable` means every admissible capacity-terminal state is ordinarily
stable. Only positive outdegree is assumed. A case the prose never mentioned
surfaced in the assembly: a live self-loop. It needs no witness, because
well-foundedness already excludes it. The census's three-condition exactness
is now a compiled theorem rather than a finite result. See
[`revisions/0.9.0-characterization-compiled.md`](revisions/0.9.0-characterization-compiled.md).

## A capacitated sink collapses everything (revision 0.7.0)

The sink was assumed absorbing throughout. If it instead holds chips under any
finite capacity, transfer holds **only when no vertex can ever fire**. Every
firing now fills something capacitated, so the all-full state — sink included —
is capacity-terminal, and with a live vertex it is not ordinarily stable. No
choice of vertex or sink capacity escapes, because the witness is built from the
capacities themselves (`capped_sink_breaks_transfer`, `no_live_all_stable`).

Census at sink capacities 0, 1, 2 and 4, `n <= 3`: exact agreement with "no
vertex live" in all 1,789,740 cases,
both populations populated, the all-full witness checked directly on every live
system, and systems that transfer with the absorbing sink but fail at every
finite cap (17,594 of them) — so the cap, not some prior failure, is what
breaks them. See
[`revisions/0.7.0-capacitated-sink.md`](revisions/0.7.0-capacitated-sink.md).

## What remains unresolved

- **Novelty is not assessed.** The capacity rule is classical finite-capacity
  Petri-net semantics and the ordinary theory is classical; only the weighted
  threshold and its preservation argument are at issue. A bounded prior-art
  search located no match and is recorded in [`review/PRIOR_ART.md`](review/PRIOR_ART.md).
- No external independent verification. The second implementation here is
  separately written but not externally authored.
- ~~Non-absorbing sinks are out of scope.~~ Settled negatively in revision 0.7.0:
  a capacitated sink admits transfer only when no vertex is live.
- ~~Whether `b(v) = max_u m(u,v)` is *necessary* at receivers of multiplicity
  one beyond `C(v) >= d(v)`.~~ Settled, and had been since revision 0.4.0: at a
  unit receiver the bound is exactly `C(v) >= d(v)`, sufficient by the transfer
  theorem and necessary by `bound_necessary_at_unit_arc`. See
  [`revisions/0.6.0-unit-receivers.md`](revisions/0.6.0-unit-receivers.md).

## Smallest decisive tests

- **Against the theorem:** an ordered multigraph satisfying the bound with a
  capacity-terminal state differing from its ordinary normal form.
- **Against sharpness:** a receiver of incoming multiplicity `k >= 2` where
  `C(v) = d(v) + k - 2` still preserves every terminal state.
- **Against novelty:** a reference proving the same preservation statement,
  with an explicit translation of capacity, threshold and transfer semantics.

## Reproduction

```text
python -B discoveries/dynamics/weighted-capacity-chip-firing/verification/run_checks.py
```

With the pinned toolchain available:

```text
python -B discoveries/dynamics/weighted-capacity-chip-firing/verification/lean/replay.py --build
```

## Repository map

- `argument/`: the exact model, the obstruction lemma, and both theorems in prose.
- `verification/lean/`: the Lean 4.35.0 sources, custody audit and replay driver.
- `verification/reference/`: the finite bound search with its transfer and
  confluence controls, the exactness census, the well-foundedness check
  with its hypothesis ablation, and the capacitated-sink census.
- `verification/independent/`: a separately written check of the theorem's conclusion.
- `evidence/`: search output, independent-check output, and the Lean receipt.
- `review/`: the bounded prior-art note and its recorded queries.
- `revisions/`: a search defect caught by the controls before any claim was registered.
