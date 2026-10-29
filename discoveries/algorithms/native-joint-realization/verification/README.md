# Verification boundary

From the repository root:

```text
python -B tools/verify_iteration_snapshot.py
```

This verifies digests of imported local records, source-state identity, promotion links, and discovery-to-claim bindings. It does not invoke Lean or re-run the exact audits described by those records.

The next integration gate is a portable pinned Lean/Lake project containing the full required source definitions, proof dependency closure, target list, no-escape court, and exact audit sources. The full candidate must replay from a clean checkout. Separately implemented finite checks remain project self-verification until external reproduction is recorded.
