# Bootstrap iteration evidence, through Cycle 17

As of 2026-10-28, research is paused. The integration roadmap remains open.

These are exact copies of local harness summaries, promotion decisions, and the Cycle 17 state. [SNAPSHOT.json](SNAPSHOT.json) lists file digests, the local harness commit, the state root, and discovery-to-claim bindings. The source harness commit is `1bffd8da123a509e08dd4c293bb18f3665e5963b`.

## What each record supports

| Local result | Record | Present review boundary |
|---|---|---|
| Native centered vanishing and A=0 collapse | [B5-M3 replay summary](B5-M3-exact-replay-r5-summary.json) and [decision](B5-M3-exact-replay-r5-decision.json) | Fresh replay passed locally with 80 files verified before compile and after extraction; the archive is not imported here. |
| Explicit parity coefficients and integer translations | [B5-M7 summary](B5-M7-parity-coefficient-closed-form-summary.json) and [decision](B5-M7-parity-coefficient-closed-form-decision.json) | Local compiled proofs and 324 exact cases; full checkout replay pending. |
| Native entry equals master numerator | [Source bridge summary](B5-K1-native-source-bridge-summary.json) and [decision](B5-K1-native-source-bridge-decision.json) | Source correspondence under the exact orbit and mismatch hypotheses; 4,212 audit tuples. |
| Shared recurrence kernel | [Kernel summary](B5-K1-master-numerator-bcm1-summary.json) and [decision](B5-K1-master-numerator-bcm1-decision.json) | Value proofs and 7,131 exact cases; arithmetic counts later formalized in Cycle 15. |
| BCM-1 arithmetic semantics | [Cost summary](B5-K1-bcm1-cost-semantics-summary.json) and [decision](B5-K1-bcm1-cost-semantics-decision.json) | Exact scalar counts under declared exclusions, not total runtime. |
| Total executable joint matrix | [Total realization summary](B5-K1-executable-joint-bcm1-summary.json) and [decision](B5-K1-executable-joint-bcm1-decision.json) | Every cell equals the source joint; the initial orbit decision was exhaustive. |
| Coordinatewise orbit decision | [Coordinate summary](B5-K1-coordinate-orbit-bcm1-summary.json) and [decision](B5-K1-coordinate-orbit-bcm1-decision.json) | Replaces exhaustive orbit enumeration while preserving values; comparison costs remain uncounted. |
| Pause and continuation | [Cycle 17 state](CYCLE-0017-state.json) | State root `e12c7114704964b03354fd0a2e8c6ba5786128ca3579977a745dd9efc6fc1245`. |

## Interpretation

These reports preserve their original bytes, including the obligations that were open when each report was produced. Read them chronologically: later decisions close some earlier obligations. On 2026-10-28 the owner confirmed the repository's public visibility and authorized uploading the prepared update. The historical restriction on remote updates is superseded for this upload; the research pause continues.

Some summaries also list supporting lemmas or static audits. Only the claim IDs explicitly named in a linked promotion decision receive that decision's standing; the snapshot does not promote every ancillary summary claim.

Run `python -B tools/verify_iteration_snapshot.py` to check file custody and claim bindings. A PASS verifies the copied records and their internal links. It does not verify the absent source tree, rebuild Lean, reconstruct the source ledger, establish novelty, or constitute external independent review.

The M3 replay used Lean 4.34.1 and Mathlib's pinned content-addressed cache. This is different from rebuilding every dependency from source. The later K1 chain has local compiled evidence but does not yet have an equivalent complete cold-replay envelope in this repository. These distinctions are acceptance gates in the [integration roadmap](../../../docs/INTEGRATION_ROADMAP.md).
