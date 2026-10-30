# Owner-fiber structure and support

> **Pipeline stage:** `QUALIFYING`  
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`, `REVISED`

Permanent discovery ID: `CBMD-COMB-OWNER-FIBER-001`

## Exact candidate claim

For a fixed covered target and requested owner, under the stated full-head coherence and orbit-head injectivity premises, the fixed-owner sum has at most one nonzero contributing source row: the row at the orbit candidate determined by the target and owner. For sums of target rows, contributors per owner are bounded by the number of distinct `(block, orbit-class)` pairs. Coherence is needed on active coordinates; dropping it at an active coordinate admits a counterexample.

## Current standing

A standalone verifier is now present ([`verification/owner_fiber.py`](verification/owner_fiber.py)),
importing nothing from the archive. It finds no violation of the unique-contributor
statement over 480 fibers at `Q=2` and 1,728 at `Q=3`, with 48 and 288
off-diagonal contributors respectively, and the candidate lookup predicts the
contributing column in every single-contributor fiber. The class-count bound for
target sums holds over 1,230 sums and is attained 54 times. Breaking coherence at
one active coordinate produces two contributors, as the claim requires.

Two degeneracy traps are recorded, one of them new: a non-degenerate *object*
does not imply a non-degenerate *test population*. See
[`revisions/0.2.0-standalone-verifier.md`](revisions/0.2.0-standalone-verifier.md).

What is still missing is the binding to the exact packed source definitions, and
multi-block packing is not modelled.

## Next obligation

State and compile the correspondence to the packed source definitions,
preserving the missing-address, first-occurrence, repeated-incidence,
uncovered-target and exact-owner branches; or give the smallest counterexample.

## Nonclaims

No native SAT speedup, source-code refinement theorem, novelty determination, or specialist review is claimed.
