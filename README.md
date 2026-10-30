<p align="center">
  <img src="assets/mosaic-rainbow-sun.png" alt="Mosaic rainbow sun logo" width="168">
</p>

# Constraint-Bound Mathematical Discovery (CBMD)

**A Mosaic Open Research repository**

Public provisional mathematics for verification, correction, or disproof.

This public repository presents selected CBMD research for verification, correction, or disproof. Release v0.1 packages a portable review toolkit around the provisional research; it is not a mirror of the internal CBMD archive. Each research line has an explicit standing, reproducible evidence where available, and visible remaining obligations.

## What CBMD means

**CBMD stands for Constraint-Bound Mathematical Discovery.** It is a research method for pursuing mathematical possibilities while keeping the claim boundary explicit: candidate transformations are stated, preservation obligations are recorded, computations are made reproducible where possible, and failures or counterexamples remain part of the research record.

“Discovery” here names the inquiry process, not a guarantee that every generated statement is new or true. A CBMD artifact is provisional until its stated obligations are discharged, and neither the workflow nor the Mosaic branding substitutes for proof, specialist review, novelty review, or publication.

## Current iteration: v0.1 toolkit and provisional finite dynamics

The original complexity investigation remains paused after Cycle 17. The v0.1 integration packages the governed harness, exact reference evaluator, minimal native Lean source closure, pinned replay driver, and public discovery dossiers in one checkout. A separate finite-dynamics line now adds a source-bound Lean theorem and independently reproduced finite evidence for capacity-blocked chip-firing. The [dated evidence snapshot](evidence/iterations/bootstrap-2026-10/README.md) remains the immutable bootstrap record; the [integration roadmap](docs/INTEGRATION_ROADMAP.md) distinguishes the completed toolkit work from the mathematical remainder.

| Layer | Meaning | Current outcome |
|---|---|---|
| CBMD | Constraint-Bound Mathematical Discovery, the research method | Claims, corrections, adverse tests and remaining obligations stay visible. |
| Governed harness | Software operating that method | Portable execution custody, evidence checks and claim ceilings; UCM native proof adapter remains unbound. |
| Complexity investigation | Mathematics about the pinned source entries and joint matrix | The minimal public Lean envelope recompiles the native chain under exact pins. |
| BCM-1 | Declared arithmetic cost model used to count that evaluator's core | Exact counts of multiplications, divisions and additions; whole-algorithm cost remains open. |

The result chain establishes native centered vanishing and A=0 collapse, an explicit parity-coefficient formula, a source-to-master-numerator identity, a recurrence evaluator with checked arithmetic counts, and a total joint realization using coordinatewise orbit compatibility. The bootstrap snapshot binds the original reports; `proofs/native/` now carries the minimal public sources and exact replay boundary.

The parity identification reduces to classical Krawtchouk ingredients. Source-specific novelty remains unassessed. The ECH review request is a separate investigation and retains its unresolved geometric transport question.

Start with the [toolkit guide](docs/TOOLKIT.md), the [native evaluator dossier](discoveries/algorithms/native-joint-realization/README.md), or the [CBMD method and harness guide](methods/governed-discovery/README.md). Reviewers can challenge the [recorded corrections](docs/CORRECTIONS.md) alongside the positive results.

## Toolkit v0.1

```text
python -B tools/qualify_repository.py
```

That one command checks the repository structure, every review-ready discovery, all 37 harness tests, the standalone finite reference audit and mutations, and formal-source custody. The full Lean replay is deliberately separate because it installs or uses pinned compiler dependencies:

```text
python -B tools/replay_lean.py --prepare --fresh
```

The harness ships with execution disabled. Its local-workspace example, the reference evaluator CLI, and the exact distinction between source custody and proof recompilation are documented in the [toolkit guide](docs/TOOLKIT.md). Release notes and retained limits are in [RELEASE_NOTES_v0.1.0.md](RELEASE_NOTES_v0.1.0.md).

## Current discoveries

<!-- BEGIN GENERATED DISCOVERY INDEX -->

### Current review-ready discoveries

| ID | Discovery | Claim standing | Most valuable open question |
|---|---|---|---|
| `CBMD-ECH-G2-LS-001` | [Genus-two low-sector pairing](discoveries/ech/genus-two-low-sector/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED`<br>`GEOMETRIC_TRANSPORT_UNRESOLVED` | Determine whether the cap/fill composition formula applies to the unstable initial-sector representatives with the asserted classes, signs, and orientations. |
| `CBMD-COMB-PARITY-AMPLITUDE-001` | [Classical Krawtchouk identification and native vanishing](discoveries/combinatorics/parity-amplitude-spectrum/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`REVISED` | Obtain an independent source-specific derivation and convention audit; the targeted prior-art assessment is done and recorded, naming the object as the binary Krawtchouk polynomial at a negative argument, placing the centered vanishing as a published root fact, and withdrawing the availability of orthogonality. |
| `CBMD-ALG-AMPLITUDE-COST-001` | [Reference amplitude cost model (no native speedup claim)](discoveries/algorithms/reference-amplitude-cost-model/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED` | Review the reference-only cost model and parameter regimes; the successor native evaluator is tracked separately. |
| `CBMD-ALG-NATIVE-JOINT-001` | [Source-equal joint evaluator and BCM-1 arithmetic counts](discoveries/algorithms/native-joint-realization/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT` | Bind one executable native consumer and charge the complete per-cell and traversal route before making any speed claim. |
| `CBMD-DYN-CAPACITY-FIRING-001` | [Finite-capacity chip-firing preservation on ordered DAGs](discoveries/dynamics/finite-capacity-chip-firing/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`SOURCE_BOUND_COMPILED`<br>`EXACT_MODEL_VERIFIED`<br>`INDEPENDENTLY_REPRODUCED` | Determine whether the weighted successor's prior art is settled; the sharp weighted candidate C(v) >= d(v) + max_u m(u,v) - 1 is now compiled as CBMD-DYN-WEIGHTED-CAPACITY-001. |
| `CBMD-DYN-WEIGHTED-CAPACITY-001` | [Capacity-blocked chip-firing: sharp weighted bound and a live-set characterization](discoveries/dynamics/weighted-capacity-chip-firing/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`SOURCE_BOUND_COMPILED`<br>`EXACT_MODEL_VERIFIED`<br>`INDEPENDENTLY_REPRODUCED` | Obtain an external review of the Lean-to-prose correspondence, and read Devillers 1990 on capacity semantics before any novelty claim. The characterization is now one compiled equivalence; what remains unmatched in the literature is the weighted threshold and the multiplicity-indexed capacity condition. |
| `CBMD-CON-CAPACITY-PRESERVATION-001` | [Capacity preservation in Petri nets: a characterization at one input place and coNP-completeness at two](discoveries/concurrency/capacity-preservation-boundary/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`SOURCE_BOUND_COMPILED`<br>`EXACT_MODEL_VERIFIED` | Obtain external review, read Devillers 1990 on capacity semantics before any novelty claim, and settle whether the queueing-with-blocking line covers non-conservative networks. The structural map is complete: zero conflict places and no input-less transitions is polynomial (characterization compiled); one conflict place, two consumers per place, or input-less transitions is each coNP-complete (reductions compiled). |
| `CBMD-DYN-FIXED-STATE-001` | [Capacity-blocked chip-firing from a fixed state: strongly NP-hard on a star](discoveries/dynamics/fixed-state-capacity-chip-firing/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`SOURCE_BOUND_COMPILED`<br>`EXACT_MODEL_VERIFIED` | Prove or refute the residue-witness conjecture for instances with no witness of a compiled shape (smallest found: B = 10 with 2, 4x9; B = 15 with 3, 6x8), e.g. via the one-step block lemma; determine FIXED-BAD on general graphs, whether FIXED-GOOD is in NP in general or hard with unit multiplicities; obtain external review. |
| `CBMD-COMB-DET-ZECK-001` | [Deterministic Zeckendorf games: Split Smallest exactly, Combine Smallest's constant](discoveries/combinatorics/deterministic-zeckendorf-games/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED`<br>`CONJECTURE` | Independent review of the Combine Smallest constant proof (§5), then Lean formalization of the SS and CS counter lemmas. |

### Candidate pipeline

| ID | Discovery | Claim standing | Stage | Next obligation | Promotion blockers |
|---|---|---|---|---|---|
| `CBMD-COMB-OWNER-FIBER-001` | [Owner-fiber structure and support](discoveries/combinatorics/owner-fiber-structure/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED`<br>`REVISED` | `QUALIFYING` | State and compile the correspondence to the packed source definitions, preserving the missing-address, first-occurrence, repeated-incidence, uncovered-target and exact-owner branches; the source is not in this repository, so this needs the archive. The unique-contributor statement itself is now compiled. | source-bound formal correspondence not stated; novelty unassessed |
| `CBMD-ALG-RESIDUE-LIFT-001` | [Residue and lift transport boundaries](discoveries/algebra/residue-lift-transport-boundaries/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED`<br>`REVISED` | `QUALIFYING` | Extract and independently replay the inherited selected-degree-six source fixture at residue and two lifted precisions, binding every ring, node, centre, amplitude and source-row parameter. The digit and regularity questions are both answered: the residue by a two-state carry automaton, the valuation by the published trichotomy of Shu and Yao and of Sobolewski once the amplitude is seen to be a polynomial in N. | inherited degree-six source fixture not yet extracted; independent source-correspondence check open; novelty unassessed |

<!-- END GENERATED DISCOVERY INDEX -->

Statuses describe the evidence currently present in this repository. They are not endorsements, peer review, or claims of novelty.

## How to navigate

Each public result lives at:

```text
discoveries/<field>/<discovery-slug>/
```

Every discovery begins with its own `README.md` and `CLAIM.json`. The readable argument, executable material, evidence, review activity, and revisions remain separate:

```text
argument/       Written mathematical argument
explorer/       Portable explanatory or numerical instruments
verification/   Reproduction and adverse-control checks
evidence/       Receipts produced by declared checks
review/         Public review dispositions, not private correspondence
revisions/      Supersession notes and correction records
```

The [repository architecture](docs/ARCHITECTURE.md) explains the invariants. The [candidate-discovery pipeline](docs/PIPELINE.md) defines admission and promotion. The [integration roadmap](docs/INTEGRATION_ROADMAP.md) is the current work plan. The [earlier refactor plan](docs/REFACTOR_PLAN.md) records the repository bootstrap history.

## What the evidence states

The repository uses explicit [claim states](docs/CLAIM_STATES.md). In particular:

- `EXACT_MODEL_VERIFIED` means the declared algebra or finite model passed its stated checks.
- `GEOMETRIC_TRANSPORT_UNRESOLVED` means the model has not been identified with the intended geometric theory.
- `SPECIALIST_REVIEWED` is reserved for a recorded review by a named specialist who has agreed to be identified.
- `REFUTED` and `SUPERSEDED` remain visible; they are not deleted from the research history.

Git history records repository changes. It does not, by itself, prove mathematics or establish scholarly priority.

## How to challenge a result

The most useful contributions are precise and falsifiable:

- a smallest counterexample;
- the first invalid inference or missing hypothesis;
- a reproduction failure with the exact environment and command;
- a source or convention mismatch;
- a prior-art match with the coordinate correspondence;
- an independent derivation of the same result.

Use the structured issue forms under [`.github/ISSUE_TEMPLATE`](.github/ISSUE_TEMPLATE/). Open-ended mathematical conversation may use repository Discussions once enabled.

## Reproduce the repository checks

Python 3.12+ is sufficient for the default checks:

```text
python -B tools/qualify_repository.py
```

The grid-audit command checks the implemented model's extended block structure and the evidentiary reach of its adverse control. The browser-level explorer check is optional and additionally requires Node.js, Playwright, and a supported installed browser. No browser or network service is required for the default qualification. The iteration-snapshot check verifies copied historical records and claim bindings; the separate Lean replay recompiles the public proof envelope.

## Add another discovery

1. Copy `templates/discovery/` to `discoveries/<field>/<slug>/`.
2. Assign a permanent discovery ID and complete `CLAIM.json`.
3. Add one registry entry to `DISCOVERIES.json`; the README table is generated from it.
4. Put claims, executable checks, receipts, reviews, and revisions in their designated directories.
5. Run `python -B tools/render_discovery_index.py --write` and `python -B tools/qualify_repository.py`.
6. Complete the [publication checklist](docs/PUBLICATION_CHECKLIST.md) before proposing a public release.

Adding ordinary supporting files inside an existing discovery does not require changing the global architecture.

## Public boundaries

- Internal canonical packages, private correspondence, unpublished third-party texts, credentials, and personal machine paths are excluded.
- A public review packet must not imply that a prospective reviewer participated or endorsed the work.
- AI assistance is disclosed in [AI_DISCLOSURE.md](AI_DISCLOSURE.md).
- The repository is public by the owner's authorization. A general reuse license remains pending; the current rights and branding boundaries are recorded in [LICENSE.md](LICENSE.md).
- The Mosaic name and rainbow sun identify the project; their provenance and separate reuse boundary are recorded in [BRANDING.md](BRANDING.md).

## Author and standing

Research direction and authorship: Adam Ableman Mazurk. Repository preparation and substantial portions of the mathematical development used AI assistance. Every discovery carries its own more specific provenance and nonclaims.

These provisional research snapshots and the v0.1 toolkit are available in the public GitHub repository `AblemanMosaic/cbmd-open-research`. Public visibility and a release tag do not establish mathematical review, novelty, or resolution of the listed open obligations.
