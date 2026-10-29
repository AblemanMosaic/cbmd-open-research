# CBMD Research Toolkit v0.1.0

This is the first functional public toolkit release of Constraint-Bound Mathematical Discovery. It packages the research-facing dossiers together with three executable layers:

- a governed operation harness for bounded local runs and evidence custody;
- a standalone exact Python evaluator with independently structured finite oracles and mutation controls;
- a pinned Lean/Lake source envelope for the native vanishing, coefficient, source-bridge, BCM-1 evaluator, cost-vector, total-joint, and coordinate-orbit results.

The release is review infrastructure for provisional mathematics. It is not peer review, an external independent reproduction, a novelty determination, a total SAT-runtime theorem, or a resolution of the ECH geometric transport question.

## Fast verification

From an extracted release or checkout with Python 3.12+:

```text
python -B tools/qualify_repository.py
```

For the formal replay, install the pinned Lean toolchain and Git, then run:

```text
python -B tools/replay_lean.py --prepare --fresh
```

The network-using `--prepare` mode acquires only the revisions pinned by `proofs/native/lake-manifest.json`. The source-custody check runs before dependency acquisition or compilation.

## Boundaries retained at release

- BCM-1 counts the scalar recurrence arithmetic; it excludes coordinate comparison, mismatch and active-set construction, traversal, allocation, bit cost, and consumer cost.
- The standalone Python verifier is project-authored finite evidence, not a second proof assistant or external verifier.
- The harness is a single-writer recorder, not an operating-system sandbox or recursive process-tree supervisor.
- The native proof replay checks the bundled statements and their logical-dependency ceiling; it does not establish source-specific novelty or a deployed end-to-end speedup.
- The ECH explorer and dossier remain a request for specialist review, with geometric transport unresolved.
