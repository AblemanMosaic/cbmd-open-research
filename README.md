<p align="center">
  <img src="assets/mosaic-rainbow-sun.png" alt="Mosaic rainbow sun logo" width="168">
</p>

# Constraint-Bound Mathematical Discovery (CBMD)

**A Mosaic Open Research repository**

Public provisional mathematics for verification, correction, or disproof.

This public repository presents selected CBMD research for verification, correction, or disproof. It contains provisional research snapshots, with no tagged release yet issued, and is not a mirror of the internal CBMD archive. Each research line has an explicit standing, reproducible evidence where available, and visible remaining obligations.

## What CBMD means

**CBMD stands for Constraint-Bound Mathematical Discovery.** It is a research method for pursuing mathematical possibilities while keeping the claim boundary explicit: candidate transformations are stated, preservation obligations are recorded, computations are made reproducible where possible, and failures or counterexamples remain part of the research record.

“Discovery” here names the inquiry process, not a guarantee that every generated statement is new or true. A CBMD artifact is provisional until its stated obligations are discharged, and neither the workflow nor the Mosaic branding substitutes for proof, specialist review, novelty review, or publication.

## Current iteration: research paused, integration in progress

The mathematical investigation is paused after Cycle 17. The [integration roadmap](docs/INTEGRATION_ROADMAP.md) defines the work needed to freeze a reproducible review snapshot and prepare the next investigation. This README and the [dated evidence snapshot](evidence/iterations/bootstrap-2026-10/README.md) record the latest local results; packaging the complete newer proof chain for replay from this repository is still open.

| Layer | Meaning | Current outcome |
|---|---|---|
| CBMD | Constraint-Bound Mathematical Discovery, the research method | Claims, corrections, adverse tests and remaining obligations stay visible. |
| Governed harness | Software operating that method | Local execution custody, evidence checks and claim ceilings; UCM native proof adapter remains unbound. |
| Complexity investigation | Mathematics about the pinned source entries and joint matrix | Local proofs connect the native definition to an executable evaluator. |
| BCM-1 | Declared arithmetic cost model used to count that evaluator's core | Exact counts of multiplications, divisions and additions; whole-algorithm cost remains open. |

The local result chain establishes native centered vanishing and A=0 collapse, an explicit parity-coefficient formula, a source-to-master-numerator identity, a recurrence evaluator with checked arithmetic counts, and a total joint realization using coordinatewise orbit compatibility. The evidence snapshot binds these reports to source hashes, claim IDs and promotion roots. It does not itself recompile Lean.

The parity identification reduces to classical Krawtchouk ingredients. Source-specific novelty remains unassessed. The ECH review request is a separate investigation and retains its unresolved geometric transport question.

Start with the [integration roadmap](docs/INTEGRATION_ROADMAP.md), the [native evaluator dossier](discoveries/algorithms/native-joint-realization/README.md), or the [CBMD method and harness guide](methods/governed-discovery/README.md). Reviewers can challenge the [recorded corrections](docs/CORRECTIONS.md) alongside the positive results.

## Current discoveries

<!-- BEGIN GENERATED DISCOVERY INDEX -->

### Current review-ready discoveries

| ID | Discovery | Claim standing | Most valuable open question |
|---|---|---|---|
| `CBMD-ECH-G2-LS-001` | [Genus-two low-sector pairing](discoveries/ech/genus-two-low-sector/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED`<br>`GEOMETRIC_TRANSPORT_UNRESOLVED` | Determine whether the cap/fill composition formula applies to the unstable initial-sector representatives with the asserted classes, signs, and orientations. |
| `CBMD-ALG-AMPLITUDE-COST-001` | [Reference amplitude cost model (no native speedup claim)](discoveries/algorithms/reference-amplitude-cost-model/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED` | Review the reference-only cost model and parameter regimes; the successor native evaluator is tracked separately. |

### Candidate pipeline

| ID | Discovery | Claim standing | Stage | Next obligation | Promotion blockers |
|---|---|---|---|---|---|
| `CBMD-COMB-OWNER-FIBER-001` | [Owner-fiber structure and support](discoveries/combinatorics/owner-fiber-structure/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT` | `CLAIM_BOUND` | Import a standalone non-degenerate reference verifier and reproduce the fixed-target owner-fiber identity from a clean checkout. | public standalone verifier not yet imported; native source correspondence remains unproved; targeted novelty review remains unperformed |
| `CBMD-COMB-PARITY-AMPLITUDE-001` | [Classical Krawtchouk identification and native vanishing](discoveries/combinatorics/parity-amplitude-spectrum/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`REVISED` | `QUALIFYING` | Import and replay the completed local centered-vanishing, A=0 and parity-coefficient proofs from this checkout. | complete newer proof sources and replay envelope not yet imported; local receipts do not recompile Lean here; source-specific novelty and external review remain unassessed |
| `CBMD-ALG-NATIVE-JOINT-001` | [Source-equal joint evaluator and BCM-1 arithmetic counts](discoveries/algorithms/native-joint-realization/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT` | `QUALIFYING` | Package the source-to-evaluator Lean chain and exact audits for clean-checkout replay; total-cost analysis remains separate. | newer Lean sources and pinned dependency envelope not yet staged; snapshot check verifies receipts only; whole-cell and whole-algorithm costs remain unproved; external review and novelty assessment remain open |
| `CBMD-ALG-RESIDUE-LIFT-001` | [Residue and lift transport boundaries](discoveries/algebra/residue-lift-transport-boundaries/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT` | `CLAIM_BOUND` | Extract the smallest source-bound example separating integer, residue-ring, and lifted zero sets under explicit ring and precision hypotheses. | standalone public counterexample has not been extracted; ring, precision, node, and source-identity hypotheses need one bounded statement; novelty remains unassessed |

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

Python 3.10+ and Node.js 18+ are sufficient for the default checks:

```text
python -B tools/qualify_repository.py
```

The grid-audit command checks the implemented model's extended block structure and the evidentiary reach of its adverse control. The browser-level explorer check is optional and additionally requires Playwright plus a supported installed browser. No browser or network service is required to inspect the Markdown or run the existing exact-model checks. The iteration-snapshot check verifies copied records and claim bindings; it is not a Lean replay.

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

These provisional research snapshots are available in the public GitHub repository `AblemanMosaic/cbmd-open-research`. Public visibility does not establish mathematical review, novelty, or completion of the integration roadmap. No GitHub release has been issued.
