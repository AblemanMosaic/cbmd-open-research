# Native Lean proof envelope

This directory is the minimal public source envelope for nine CBMD proof targets. It contains 41 transitive OAI source modules, an audit module, exact Lean and mathlib pins, and a source manifest. It does not contain compiled `.olean` files or a pre-existing project build.

The proof levels are intentionally separate:

1. `python tools/verify_proof_sources.py` verifies custody, hashes, import closure, fixed pins, and the absence of proof-escape tokens in code. It does not invoke Lean.
2. `python tools/replay_lean.py --fresh` recompiles the public OAI targets and runs `OAI/CBMDReplay.lean` with warnings treated as errors. It also checks the reported axiom set against the manifest allowlist.
3. `python tools/replay_lean.py --prepare --fresh` may acquire the pinned dependency checkout before performing the same replay. This is the network-using path.

The package proves statements about the native `LayoutNumerator.entry`, a closed BCM1 evaluator, its declared reference-model operation counts, and coordinate-orbit agreement. It does **not** prove a total SAT-runtime improvement, a native whole-route crossover, novelty, or any ECH geometric transport statement.

## Provenance and licensing

The original OAI files are pinned to `openai/math` commit `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, with later CBMD modules and modifications identified in `SOURCE_MANIFEST.json`. The upstream source is Apache-2.0 licensed; its exact license text is retained as `LICENSES/OPENAI_MATH_APACHE_2.txt`. The repository's own material remains governed by the root `LICENSE.md`.
