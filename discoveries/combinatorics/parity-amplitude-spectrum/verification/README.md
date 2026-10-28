# Verification status

The isolated integer cancellation proof is in `lean/CenteredVanishingCore.lean`. Its pinned local compilation receipt is in `../evidence/LEAN_CENTERED_CORE_RECEIPT.json`; `lean/verify_receipt.py` checks source custody and the no-escape boundary using only Python's standard library.

This does not replay Lean from a clean checkout and does not prove correspondence to the native `LayoutNumerator.entry` definition. Those remain the next obligations.

The first native closed-form candidate is now refuted by `lean/EntryClosedFormCounterexample.lean`. The exact finite audit and two mutant families are in `reference-model/check_entry_closed_form.py`; the correction receipt explains the revised guarded formula. Neither artifact proves that revised formula generally.

`lean/EntryClosedFormOrbit.lean`, `lean/EntryClosedFormDifference.lean`, and `lean/EntryClosedFormCounting.lean` contain seven compiled, no-escape source-bridge components. These now include inactive-coordinate cancellation and the exact guarded powerset count. `verify_entry_closed_form_bridge.py` checks their byte custody and escape boundary. A clean checkout still cannot replay Lean because the pinned upstream source tree and Lake environment are not vendored here.
