# Correction and disproof policy

Corrections are research output.

When a public objection is accepted:

1. Record the affected permanent claim ID and exact released version.
2. State whether the result is narrowed, corrected, refuted, or superseded.
3. Preserve the objection, decisive evidence, and maintainer disposition.
4. Update the discovery README and `CLAIM.json` without rewriting prior releases.
5. Add a revision note linking predecessor and successor.
6. Re-run all applicable checks and issue a new release only after the updated envelope passes.

Negative results, source mismatches, and prior-art identifications receive the same durable treatment as positive results.

## Bootstrap iteration correction register

| Correction | Current disposition | Evidence or integration obligation |
|---|---|---|
| Original B5-E1 fixtures exercised no off-diagonal contributors | Narrow the historical evidence claim; require nondegenerate off-diagonal fixtures | Owner-fiber source custody retains the original obstruction report and corrected fixture sources; neutral standalone reproduction remains open. |
| Unguarded native binomial formula | Refuted as stated; guarded successor compiles locally | [Recorded counterexample and repair](../discoveries/combinatorics/parity-amplitude-spectrum/revisions/0.2.0-entry-closed-form-correction.md). |
| Duplicated mismatch sign and wrong cardinality in the proposed master bridge | Corrected before the local general source identity was proved | [Source bridge record](../evidence/iterations/bootstrap-2026-10/B5-K1-native-source-bridge-summary.json); import the sign audit and minimal counterexample in the replay gate. |
| Exhaustive orbit decision in the first total realization | Replaced by a proved coordinatewise criterion | [Cycle 17 record](../evidence/iterations/bootstrap-2026-10/B5-K1-coordinate-orbit-bcm1-summary.json); full costs remain open. |
| Uniform exponential-in-Q language in the frozen cost argument | Narrow to a stated joint growth regime; fixed-R enumeration is polynomial | [Parameter-regime correction](../discoveries/algorithms/reference-amplitude-cost-model/revisions/0.3.0-scope-and-parameter-regime.md). |
| Earlier native vanishing and scalar bridge obligations shown as still mathematically unfinished | Completed locally; checkout integration remains unfinished | [Dated local receipts](../evidence/iterations/bootstrap-2026-10/README.md) and [integration gates](INTEGRATION_ROADMAP.md). |
| Windows checkout changed Lean source bytes under automatic newline conversion | Pin `.lean` files to LF in `.gitattributes`; retain the original receipts and their hashes | First clean-clone qualification exposed the mismatch; a successor clean checkout must pass without editing source or relaxing digest checks. |
| First weighted sharpness sweep lowered capacity at every vertex at once | Narrowed before registration; sources at a capacity below their own outdegree can never fire, so the sweep reported no failure for a degenerate reason | [Defect record](../discoveries/dynamics/weighted-capacity-chip-firing/revisions/0.1.0-degenerate-sweep-defect.md); the published sweep lowers one receiver at a time and carries a positive control. |
| Weighted checks first gated on nonconfluence | Corrected to gate on the transfer property | A capacity system can be confluent and still terminate away from the ordinary normal form; the smallest `C=d` witness has one normal form. Recorded in the weighted dossier README. |
| Finite-dynamics Q8 qualification depended on an injected repository `PYTHONPATH` | Preserve Q8 as failed; repair both older producers for direct-path launch | [Qualification-path repair](../discoveries/dynamics/finite-capacity-chip-firing/revisions/0.1.0-qualification-path-repair.md); Q9 and Q10 passed without the injected path. |

The negative crossover and the neutral ring-operation result are now exported in
[the cost-model neutral results](../discoveries/algorithms/reference-amplitude-cost-model/argument/NEUTRAL_RESULTS.md),
and the rejected low-digit criterion in
[the residue/lift separation](../discoveries/algebra/residue-lift-transport-boundaries/argument/SEPARATION.md),
each bound to evidence reproducible from this checkout. Export does not make them
externally reviewed or novelty-assessed; both remain open for all three.

## Second iteration correction register

Every entry below was caught before the affected claim was registered, and all
but two are defects in the **evidence apparatus** rather than in the
mathematics. That distribution is the finding: a wrong theorem announces
itself, while a control that tests nothing passes quietly.

| Correction | Current disposition | Evidence or obligation |
|---|---|---|
| A census compared `preserves(...)`, which returns a `(verdict, witness)` pair in that dossier's model, against a boolean | Fixed before registration; every case had "disagreed", so the zero-disagreement gate failed loudly rather than passing | [All-full obstruction](../discoveries/concurrency/capacity-preservation-boundary/revisions/0.2.0-allfull-obstruction.md); counts after the fix match a separately written implementation exactly. |
| The flow obstruction condition first carried only clauses 1–3 | Sound but incomplete; clause 4 (some mover takes from a member) is the repair | [Flow characterization](../discoveries/concurrency/capacity-preservation-boundary/revisions/0.3.0-flow-characterization.md); smallest witness is three movers `0 → 1` at capacities `(0,0,1)`, and the clause-4 ablation is retained as a permanent control. |
| The weighted-flow procedure tested the capacity box inside the closure loop **and** guarded the seed | One check written twice: ablating either changed nothing in any box, which looked like two idle steps | [Weighted flow](../discoveries/concurrency/capacity-preservation-boundary/revisions/0.5.0-weighted-flow.md); a closure step cannot leave the box, so one test after the closure suffices. |
| A completeness lemma carried a hypothesis the linter reported unused | Symptom of leastness still being assumed outright; discharged through the inductive `Forced`, after which the hypothesis is the induction's base case | [Weighted flow](../discoveries/concurrency/capacity-preservation-boundary/revisions/0.5.0-weighted-flow.md). |
| The step rule needed a `give t ≤ cap d` guard that the reference implementation never had to state | Added; Python's signed arithmetic makes a negative threshold inert, while Lean's truncated subtraction turns it into a claimed token | [Weighted flow](../discoveries/concurrency/capacity-preservation-boundary/revisions/0.5.0-weighted-flow.md). |
| `0 < pre t (input t)` was load-bearing and unwritten | Added as an explicit hypothesis; the generators always satisfied it, so nothing was wrong, but the structure never required the named input place to be a genuine input | [Termination](../discoveries/concurrency/capacity-preservation-boundary/revisions/0.7.0-termination.md); surfaced only by compiling a step that obviously works. |
| A locality search reported 52 witnesses against a radius-1 signature that forgets which transition consumes which place | Withdrawn; proper Weisfeiler-Leman refinement separates them all | Not registered. The replacement search then returned a clean negative on boxes in which 1-WL separated **every** non-isomorphic system, so it had tested nothing; the probe now reports `VACUOUS_BOX` rather than `NOT_FOUND` for that case. |
| That locality search was run in a family where the predicate collapses | Abandoned; the all-full obstruction makes preservation a radius-0 condition there, so the family could never have refuted locality | [All-full obstruction](../discoveries/concurrency/capacity-preservation-boundary/revisions/0.2.0-allfull-obstruction.md). The question was later settled from the other direction, by hardness. |
| A valuation control was labelled by its roots in `C` when only roots in `Z_3` matter | Relabelled; `x^2 + 3x - 3` has no root in `Z_3`, so it is in the periodic branch and its rank was right to stabilize | [Valuation regularity](../discoveries/algebra/residue-lift-transport-boundaries/revisions/0.4.0-valuation-regularity.md). |
| Testing for a root in `Z_3` by Hensel survivors, before removing rational roots | Corrected; `(x+2)(x-1)` has two rational roots three apart, so the product is divisible by `9` at every lift and survivors persist with nothing behind them | [Valuation regularity](../discoveries/algebra/residue-lift-transport-boundaries/revisions/0.4.0-valuation-regularity.md); stripping first makes the test correct, and correct by compactness. |
| An anti-vacuity gate required a witness of exactly what its theorem forbids | Replaced; counting *distinct pairs inside one orbit* is what makes orbit-head injectivity non-vacuous, not counting pairs that share a head | [Unique contributor](../discoveries/combinatorics/owner-fiber-structure/revisions/0.3.0-compiled-unique-contributor.md); the first version could only ever fail. |

Two prior-art corrections from the same iteration are recorded with their
dossiers rather than here, because they narrow claims rather than repair
evidence: the capacity obstruction is a **trap** and the two enabledness
notions are Murata's **strict** and **weak** transition rules
([note](../discoveries/concurrency/capacity-preservation-boundary/review/PRIOR_ART.md)),
and the unit-weight single-output case is known in the queueing-with-blocking
literature as a cycle of full buffers, which withdraws the framing that its
exactness came from dropping reachability.

### What the register suggests about gates

Four of the entries above are controls that were themselves wrong, in three
distinct ways: a control measuring the wrong field, a control demanding a
witness its own theorem forbids, a pair of controls each masking the other,
and a control population in which the predicate was degenerate. None would
have surfaced by reading the code; each surfaced because some other gate
disagreed with it.

The practices that did the catching, stated so they can be reused:

- require each hypothesis of a conjunction to produce a failure when deleted,
  and treat "deleting it changed nothing" as a defect report rather than as
  reassurance;
- require the test population to contain instances the claim says should
  fail, not only instances it says should pass;
- when a proof and a procedure are supposed to agree, have the procedure emit
  its own certificate and check it against the proof's hypotheses, rather than
  asserting the two describe the same object;
- report a search that could not have found a counterexample as vacuous, under
  a name distinct from a search that looked and found none.
