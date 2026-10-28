# Candidate-discovery pipeline

The pipeline makes work visible without confusing visibility with proof, review, novelty, or release. `DISCOVERIES.json` is the single machine-readable index. The root README is a deterministic projection of that registry.

## Two independent axes

`pipeline_stage` records operational maturity:

| Stage | Admission rule | README group |
|---|---|---|
| `INTAKE` | Exact source and custody are retained, but no neutral public claim is ready. | Not listed. |
| `CLAIM_BOUND` | A permanent ID, exact statement, nonclaims, unresolved items, and decisive test exist. | Candidate pipeline. |
| `QUALIFYING` | Declared proof, computation, transport, engineering, and publication gates are in progress. | Candidate pipeline. |
| `REVIEW_READY` | The neutral dossier and all declared required checks pass from the repository checkout. | Current review-ready discoveries. |
| `RELEASED` | A public tag, immutable archive, and detached verification receipt exist. | Current review-ready discoveries. |
| `CLOSED` | The line is refuted, superseded, or withdrawn. | Historical closed table. |

The `status` array records claim standing. It is not inferred from the pipeline stage. A review-ready discovery may remain a conjecture or have unresolved geometric transport.

## Minimum claim-bound record

A candidate enters the README only after it has:

1. a durable discovery line, slug, and permanent CBMD ID;
2. a falsifiable statement and bounded scope;
3. explicit verified, unresolved, and nonclaim fields;
4. a smallest decisive test;
5. a next obligation and named promotion blockers;
6. neutral public wording with no private correspondence or prospective-reviewer association;
7. source custody retained outside the public projection.

## Qualification gates

Qualification examines five independent boundaries:

1. **Mathematical:** definitions, quantifiers, hypotheses, proof status, and counterexamples.
2. **Computational:** exact tests, non-degenerate fixtures, adverse controls, and deterministic regeneration.
3. **Transport:** correspondence between a checked reference model and the intended native theory.
4. **Engineering:** clean checkout, platform behavior, exact dependencies, and receipts.
5. **Publication:** licensing, attribution, citations, neutral naming, AI disclosure, and sensitive-material exclusion.

Each discovery declares executable checks in `CLAIM.json`. `tools/qualify_repository.py` runs the repository gates and all declared discovery checks without a shell. GitHub Actions runs that command on Windows and Ubuntu.

When `evidence/SOURCE_CUSTODY.json` gives a `public_copy` for an archive member, the repository validator requires that file and checks its SHA-256. A declared detached receipt is checked the same way. This keeps the readable projection tied to the sealed source without placing the full internal archive in the repository.

## Promotion procedure

1. Add or revise the discovery directory and registry row.
2. Run `python -B tools/render_discovery_index.py --write`.
3. Run `python -B tools/qualify_repository.py`.
4. Preserve failed checks and narrowed statements in the revision record.
5. Promote the stage only when its gate is satisfied; never promote a claim status merely because an engineering check passed.
6. For a public release, separately create an immutable archive and detached receipt. A Git commit alone is not a release qualification.

## Discovery-line granularity

One README row should represent one coherent external review question. Supporting lemmas and finite audits remain inside that discovery. Split a line when its claims have materially different hypotheses, proof status, transport obligations, or likely review outcomes.
