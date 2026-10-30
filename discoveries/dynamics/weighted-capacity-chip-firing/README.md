# Weighted-transfer capacity-blocked chip-firing

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

## What remains unresolved

- **Novelty is not assessed.** The capacity rule is classical finite-capacity
  Petri-net semantics and the ordinary theory is classical; only the weighted
  threshold and its preservation argument are at issue. A bounded prior-art
  search located no match and is recorded in [`review/PRIOR_ART.md`](review/PRIOR_ART.md).
- No external independent verification. The second implementation here is
  separately written but not externally authored.
- Non-absorbing sinks are out of scope.
- Whether `b(v) = max_u m(u,v)` is *necessary* at receivers of multiplicity one
  beyond `C(v) >= d(v)` is not addressed.

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
- `verification/reference/`: the finite bound search with its transfer and confluence controls.
- `verification/independent/`: a separately written check of the theorem's conclusion.
- `evidence/`: search output, independent-check output, and the Lean receipt.
- `review/`: the bounded prior-art note and its recorded queries.
- `revisions/`: a search defect caught by the controls before any claim was registered.
