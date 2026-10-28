# Repository architecture

## Design objective

The repository must make it easy to add files without weakening the distinction between claims, evidence, interpretation, review, and revision.

## Stable hierarchy

```text
discoveries/<field>/<slug>/
```

`field` is a broad mathematical area, not an evidence status or project phase. `slug` identifies one durable discovery line. Renaming a display title does not change the slug or permanent claim ID.

Each discovery has these required roots:

```text
README.md
CLAIM.json
argument/
explorer/
verification/
evidence/
review/
revisions/
```

Files may be added freely inside the appropriate root. A new top-level category requires an architecture revision because tools and readers rely on this separation.

## Pipeline and standing

Operational pipeline stage and mathematical claim standing are separate axes. `DISCOVERIES.json` records both and is the source for the generated README index. See `docs/PIPELINE.md` for stage admission rules.

A README row identifies a coherent discovery line, not every lemma or finite observation inside it. Split a line when claims have different hypotheses, proof status, transport obligations, or likely review outcomes.

## Identity layers

Keep these objects distinct:

1. The mathematical discovery line and permanent claim ID.
2. A versioned public claim statement.
3. An exact file or executable artifact.
4. A repository commit.
5. A release archive and, if later created, its archival DOI.

A shared title or Git commit does not merge these identities.

## Evidence boundary

Verification scripts state exactly what they test and what they do not test. Evidence receipts bind the check, inputs, outputs, environment where relevant, and standing. A successful executable check may raise model confidence but cannot promote a geometric or analytic claim unless that correspondence is itself proved and reviewed.

## Review boundary

`review/` contains public, attributable review dispositions or anonymized summaries that the contributor has permission to publish. Invitations, cover letters, private email, and the names of prospective reviewers do not belong in the public repository.

## Revision rule

Materially narrowed, corrected, refuted, or superseded claims receive a revision record. Do not erase a public claim to make the current state look cleaner. The current README may point readers to the successor while history and release records preserve the prior statement.
