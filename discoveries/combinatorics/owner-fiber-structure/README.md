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

Revision 0.3.0 compiles the unique-contributor statement — against an abstract
model in which support-in-orbit is a hypothesis, not against the packed source
definitions, so it does **not** confer `SOURCE_BOUND_COMPILED`; that status was
granted in 0.3.0 and withdrawn in 0.5.0
([`revisions/0.5.0-status-withdrawn.md`](revisions/0.5.0-status-withdrawn.md)). It takes exactly two
hypotheses — a nonzero source row forces the type into the target's orbit, and
a column's head word is its owner's head word — and derives the rest, including
the orbit-head injectivity that the written claim had listed as a premise. The
contributing column is proved to be the explicit candidate, which the census
could only observe. The verifier now also measures those two hypotheses against
the layouts it generates, so the proof is checked to be about this model. See
[`revisions/0.3.0-compiled-unique-contributor.md`](revisions/0.3.0-compiled-unique-contributor.md).

Revision 0.4.0 compiles the class-count bound the same way, by isolating what
it rests on: for a fixed owner, each orbit class holds at most one column. The
step from that to a count is pigeonhole and is left explicit.

Revision 0.6.0 checks both claims against the repository's frozen **packed
reference** on layouts with several blocks. The census has zero violations over
21,144 queries and 8,226 target sums. Every packed branch is exercised:
missing pair, repeated pair, uncovered target, exact-owner rejection, and a
block other than 0. Comparing rows across blocks breaks it (4,123 violations),
so the block structure is load-bearing. See
[`revisions/0.6.0-packed-reference-census.md`](revisions/0.6.0-packed-reference-census.md).

Revision 0.8.0 compiles both claims **with blocks**, proving the packing invariant from the definition of a block (rank among equal earlier labels), and bridges that definition to the packed reference ([`revisions/0.8.0-blocks-compiled.md`](revisions/0.8.0-blocks-compiled.md)).

Revision 0.9.0 compiles the row-level step (`row_support_in_orbit`), so support-in-orbit now reduces to the natively compiled amplitude fact plus a model binding ([`revisions/0.9.0-row-step-compiled.md`](revisions/0.9.0-row-step-compiled.md)).

What is still missing is a *compiled* binding to the exact packed source
definitions. One piece of it already exists in this repository's native
proof package: `entry_eq_zero_of_not_inOrbit` compiles the amplitude half of
the support-in-orbit hypothesis for the native source entry. The row-level
step, the binding of this dossier's model to the native one, and coherence do
not. See
[`revisions/0.7.0-native-counterpart-located.md`](revisions/0.7.0-native-counterpart-located.md).

## Next obligation

State and compile the correspondence to the packed source definitions,
preserving the missing-address, first-occurrence, repeated-incidence,
uncovered-target and exact-owner branches; or give the smallest counterexample.

## Nonclaims

No native SAT speedup, source-code refinement theorem, novelty determination, or specialist review is claimed.
