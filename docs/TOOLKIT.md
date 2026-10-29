# CBMD Research Toolkit v0.1

The toolkit turns the repository from a readable research snapshot into a reproducible review surface. Its components deliberately prove different things.

| Component | Command | What a pass establishes | What it does not establish |
|---|---|---|---|
| Repository qualification | `python -B tools/qualify_repository.py` | Structure, discovery checks, harness tests, finite reference audit, proof-source custody and adversarial packaging tests pass. | Lean recompilation, peer review, novelty or a total performance result. |
| Governed harness | `python -B tools/verify_harness.py` | Exact shipped source bytes and all 37 required control tests pass. | Mathematical truth, process confinement, multi-writer safety or UCM-native proof. |
| Exact reference toolkit | `python -B tools/verify_standalone.py` | The declared finite boxes agree across the recurrence, falling-factorial/interpolation/literal-expansion oracles, and nine mutations are detected. | A general proof, external independence or whole-algorithm cost. |
| Lean source custody | `python -B tools/verify_proof_sources.py` | Every public Lean input, pin and local import is bound; forbidden proof escapes are absent from code. | Compilation or the actual dependency set of a compiled theorem. |
| Lean replay | `python -B tools/replay_lean.py --prepare --fresh` | The nine targets compile from a project without prior CBMD proof objects and the audit module admits only the declared logical primitives. | A dependency build from raw compiler source, independent review, novelty or deployment. |

## Research workflow

1. Initialize a bounded local harness workspace; execution is disabled in the shipped template.
2. Admit exact inputs and create an operation request before launching a reviewed tool.
3. Retain one intent and one terminal, including failures, refusals and uncertain recoveries.
4. Run exact-model checks, mutations and Lean where each is appropriate.
5. Keep observation, evidence, interpretation and claim standing separate.
6. Update a discovery's statement, nonclaims, unresolved items and next obligation together.
7. Promote to review-ready only when all declared required checks pass from the checkout.

See [the harness guide](../software/harness/README.md), [the reference evaluator](../software/reference/README.md), and [the native proof envelope](../proofs/native/README.md) for component-specific instructions.
