# Verification status

The isolated integer cancellation proof is in `lean/CenteredVanishingCore.lean`. Its pinned local compilation receipt is in `../evidence/LEAN_CENTERED_CORE_RECEIPT.json`; `lean/verify_receipt.py` checks source custody and the no-escape boundary using only Python's standard library.

That historical receipt does not itself replay Lean. The v0.1 proof envelope separately stages and recompiles the longer native source chain.

The first native closed-form candidate is refuted by `lean/EntryClosedFormCounterexample.lean`. The exact finite audit and two mutant families are in `reference-model/check_entry_closed_form.py`; the correction receipt explains the revised guarded formula.

Six copied modules contain the historical compiled, no-escape bridge and assembly: `EntryClosedFormOrbit.lean`, `EntryClosedFormDifference.lean`, `EntryClosedFormCounting.lean`, `EntryClosedFormUnique.lean`, `EntryClosedFormSigned.lean`, and `EntryClosedFormAssemble.lean`. The last module proves the guarded formula directly against the pinned native `LayoutNumerator.entry`. `verify_entry_closed_form_bridge.py` checks byte custody and the escape boundary.

`lean/ParityReflection.lean` contains the compiled, no-escape rational-polynomial proof of the parity interpolant reflection law. `verify_parity_reflection.py` checks its exact hash, proof-escape boundary, theorem inventory, terminal root, and promotion decision.

The native centered-vanishing, A=0 collapse and coefficient corollaries are now part of the minimal public proof envelope under [`proofs/native`](../../../../proofs/native/README.md). `tools/verify_proof_sources.py` checks source custody only. `tools/replay_lean.py --prepare --fresh` performs the pinned recompilation and executable logical-dependency audit; the dedicated CI job runs that replay separately from the default finite checks.
