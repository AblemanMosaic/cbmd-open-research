# Finite-capacity chip-firing on ordered DAGs

> **Standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `SOURCE_BOUND_COMPILED`,
> `EXACT_MODEL_VERIFIED`, `INDEPENDENTLY_REPRODUCED`

Permanent claim ID: `CBMD-DYN-CAPACITY-FIRING-001`

## Exact claim

Let a finite loopless directed graph have an absorbing sink reachable from every
nonsink vertex. Assume its nonsink edges are unit edges and acyclic, and each
receiver capacity satisfies `C(v) >= d(v)`, where `d(v)` is total outdegree
including sink edges. Then capacity-blocked chip-firing terminates and every
maximal execution reaches the same state as ordinary chip-firing.

## What is established

- A complete Lean 4.35.0 theorem binds the claim to the concrete unit-edge
  update, proves lexicographic termination and local commutation, derives
  ordinary unique stabilization by a terminal form of Newman's lemma, and
  transfers that result to capacity-blocked firing.
- A primary implementation found no counterexample among 340 ordered simple
  DAGs, 5,222 capacity systems, and 420,840 admissible initial states.
- A separately written verifier reproduced the same finite box without
  importing the producer.
- Exact adverse witnesses show failure on a directed cycle and on a DAG with a
  multiplicity-two transfer.

The finite enumeration corroborates the theorem but is not its proof.

## What remains unresolved

- Novelty is not certified. The capacity rule is classical finite-capacity
  Petri-net semantics, and an equivalent theorem may exist under another name.
- External graph files are not decoded or certified by the Lean theorem;
  callers must supply the true edge relation and outdegree function.
- The weighted/parallel-edge successor is unproved. The leading candidate is
  `C(v) >= d(v) + max_u m(u,v) - 1`.

## Smallest decisive tests

- Removing acyclicity: the recorded three-vertex unit-edge system reaches two
  terminal states from `(1,1,1)`.
- Removing unit transfers: the recorded two-vertex DAG with multiplicity two
  has a capacity-terminal state containing an ordinarily unstable source.

## Repository map

- `argument/`: exact model contract and written proof.
- `verification/reference/`: producer and deterministic finite searches.
- `verification/independent/`: separately implemented finite verifier.
- `verification/lean/`: exact Lean 4.35.0 source envelope and replay driver.
- `evidence/`: source custody and the sanitized Q10 binding receipt.
- `review/`: bounded prior-art and formal-source comparison.
- `revisions/`: preserved qualification-path failure and repair.

## Reproduction

From the repository root:

```text
python -B discoveries/dynamics/finite-capacity-chip-firing/verification/verify_custody.py
python -B discoveries/dynamics/finite-capacity-chip-firing/verification/run_checks.py
python -B discoveries/dynamics/finite-capacity-chip-firing/verification/lean/replay.py --audit-only
```

With Lean/Lake available under the pinned toolchain:

```text
python -B discoveries/dynamics/finite-capacity-chip-firing/verification/lean/replay.py --build
```

## How to challenge this result

The most useful challenge is a counterexample satisfying every stated
hypothesis, the first invalid Lean-to-prose correspondence, or a prior-art match
with an explicit translation of capacity, threshold, and transfer semantics.
