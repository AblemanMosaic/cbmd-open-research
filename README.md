<p align="center">
  <img src="assets/mosaic-rainbow-sun.png" alt="Mosaic rainbow sun logo" width="168">
</p>

# Constraint-Bound Mathematical Discovery (CBMD)

**A Mosaic Open Research repository**

Public provisional mathematics for verification, correction, or disproof.

This repository is the intended public research surface for selected CBMD discovery lines. Its current GitHub home is a private staging repository, not a public release, and it is not a mirror of the internal CBMD archive. A result appears here only after it has been separated from private correspondence, assigned an explicit standing, given reproducible evidence where available, and checked for publication-sensitive material.

## What CBMD means

**CBMD stands for Constraint-Bound Mathematical Discovery.** It is a research method for pursuing mathematical possibilities while keeping the claim boundary explicit: candidate transformations are stated, preservation obligations are recorded, computations are made reproducible where possible, and failures or counterexamples remain part of the research record.

“Discovery” here names the inquiry process, not a guarantee that every generated statement is new or true. A CBMD artifact is provisional until its stated obligations are discharged, and neither the workflow nor the Mosaic branding substitutes for proof, specialist review, novelty review, or publication.

## Current discoveries

<!-- BEGIN GENERATED DISCOVERY INDEX -->

### Current review-ready discoveries

| ID | Discovery | Claim standing | Most valuable open question |
|---|---|---|---|
| `CBMD-ECH-G2-LS-001` | [Genus-two low-sector pairing](discoveries/ech/genus-two-low-sector/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED`<br>`GEOMETRIC_TRANSPORT_UNRESOLVED` | Determine whether the cap/fill composition formula applies to the unstable initial-sector representatives with the asserted classes, signs, and orientations. |
| `CBMD-ALG-AMPLITUDE-COST-001` | [Reference amplitude evaluation and cost model](discoveries/algorithms/reference-amplitude-cost-model/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`EXACT_MODEL_VERIFIED` | Bind the closed amplitude route to an executable native entry under an explicit cost model, or record the first exact source-level obstruction. |

### Candidate pipeline

| ID | Discovery | Claim standing | Stage | Next obligation | Promotion blockers |
|---|---|---|---|---|---|
| `CBMD-COMB-OWNER-FIBER-001` | [Owner-fiber structure and support](discoveries/combinatorics/owner-fiber-structure/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT` | `CLAIM_BOUND` | Import a standalone non-degenerate reference verifier and reproduce the fixed-target owner-fiber identity from a clean checkout. | public standalone verifier not yet imported; native source correspondence remains unproved; targeted novelty review remains unperformed |
| `CBMD-COMB-PARITY-AMPLITUDE-001` | [Parity-amplitude spectrum](discoveries/combinatorics/parity-amplitude-spectrum/README.md) | `PROVISIONAL_WRITTEN_ARGUMENT`<br>`REVISED` | `CLAIM_BOUND` | Prove that native delta selects exactly the active subword mismatches.erase t, then assemble the guarded entry_closed_form. | the revised guarded entry_closed_form is not yet formally proved; clean-checkout Lean replay of the copied proof modules is not yet packaged; source-specific novelty remains unassessed |
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

The [repository architecture](docs/ARCHITECTURE.md) explains the invariants. The [candidate-discovery pipeline](docs/PIPELINE.md) defines admission and promotion. The [refactor and publication plan](docs/REFACTOR_PLAN.md) records what still must happen before the first public release.

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

The grid-audit command checks the implemented model's extended block structure and the evidentiary reach of its adverse control. The browser-level explorer check is optional and additionally requires Playwright plus a supported installed browser. No browser or network service is required to inspect the Markdown or run either exact-model check.

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
- Licensing remains pending for this private release candidate; see [LICENSE.md](LICENSE.md). Private repository staging is authorized, but the repository must not be made public until the path-level license decision is complete.
- The Mosaic name and rainbow sun identify the project; their provenance and separate reuse boundary are recorded in [BRANDING.md](BRANDING.md).

## Author and standing

Research direction and authorship: Adam Ableman Mazurk. Repository preparation and substantial portions of the mathematical development used AI assistance. Every discovery carries its own more specific provenance and nonclaims.

This candidate is staged in the private GitHub repository `AblemanMosaic/cbmd-open-research`. It has not been made public and no GitHub release has been issued.
