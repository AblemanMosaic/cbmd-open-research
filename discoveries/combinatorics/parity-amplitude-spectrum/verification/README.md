# Verification status

The isolated integer cancellation proof is in `lean/CenteredVanishingCore.lean`. Its pinned local compilation receipt is in `../evidence/LEAN_CENTERED_CORE_RECEIPT.json`; `lean/verify_receipt.py` checks source custody and the no-escape boundary using only Python's standard library.

This does not replay Lean from a clean checkout. The centered cancellation core also remains separated from the native source theorem.

The first native closed-form candidate is refuted by `lean/EntryClosedFormCounterexample.lean`. The exact finite audit and two mutant families are in `reference-model/check_entry_closed_form.py`; the correction receipt explains the revised guarded formula.

Six copied modules now contain the compiled, no-escape bridge and assembly: `EntryClosedFormOrbit.lean`, `EntryClosedFormDifference.lean`, `EntryClosedFormCounting.lean`, `EntryClosedFormUnique.lean`, `EntryClosedFormSigned.lean`, and `EntryClosedFormAssemble.lean`. The last module proves the guarded formula directly against the pinned native `LayoutNumerator.entry`. `verify_entry_closed_form_bridge.py` checks byte custody and the escape boundary. A clean checkout still cannot replay Lean because the pinned upstream source tree and Lake environment are not vendored here.

`lean/ParityReflection.lean` contains the compiled, no-escape rational-polynomial proof of the parity interpolant reflection law. `verify_parity_reflection.py` checks its exact hash, proof-escape boundary, theorem inventory, terminal root, and promotion decision. This closes the reflection sub-obligation, but the native centered-vanishing corollary has not yet been compiled. A clean checkout still cannot replay Lean because the pinned upstream source tree and Lake environment are not vendored here.
