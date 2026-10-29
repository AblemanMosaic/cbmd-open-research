# Verification boundary

From the repository root:

```text
python -B tools/verify_iteration_snapshot.py
```

This verifies digests of imported historical records, source-state identity, promotion links, and discovery-to-claim bindings. It does not invoke Lean or re-run the exact audits described by those records.

The v0.1 successor gates are:

```text
python -B tools/verify_standalone.py
python -B tools/verify_proof_sources.py
python -B tools/replay_lean.py --prepare --fresh
```

The first performs the finite exact-model and mutation audit. The second verifies source custody without compiling. The third recompiles the pinned proof chain and executes the logical-dependency audit. All remain project self-verification until external reproduction is recorded.
