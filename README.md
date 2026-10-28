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

| ID | Discovery | Standing | Most valuable open question |
|---|---|---|---|
| `CBMD-ECH-G2-LS-001` | [Genus-two low-sector pairing](discoveries/ech/genus-two-low-sector/README.md) | Exact algebra model verified; geometric transport unresolved | Does the cap/fill composition formula apply to the unstable initial-sector representatives with the asserted classes, signs, and orientations? |

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

The [repository architecture](docs/ARCHITECTURE.md) explains the invariants. The [refactor and publication plan](docs/REFACTOR_PLAN.md) records what still must happen before the first public release.

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
python -B tools/validate_repository.py
python -B discoveries/ech/genus-two-low-sector/explorer/source/build.py --check
node discoveries/ech/genus-two-low-sector/verification/test_pairing_explorer.cjs
node discoveries/ech/genus-two-low-sector/verification/grid-audit/grid_audit.js
```

The grid-audit command checks the implemented model's extended block structure and the evidentiary reach of its adverse control. The browser-level explorer check is optional and additionally requires Playwright plus a supported installed browser. No browser or network service is required to inspect the Markdown or run either exact-model check.

## Add another discovery

1. Copy `templates/discovery/` to `discoveries/<field>/<slug>/`.
2. Assign a permanent discovery ID and complete `CLAIM.json`.
3. Add one registry entry to `DISCOVERIES.json` and this README table.
4. Put claims, executable checks, receipts, reviews, and revisions in their designated directories.
5. Run `python -B tools/validate_repository.py`.
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
