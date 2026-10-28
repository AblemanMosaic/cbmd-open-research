# Verification status

The isolated integer cancellation proof is in `lean/CenteredVanishingCore.lean`. Its pinned local compilation receipt is in `../evidence/LEAN_CENTERED_CORE_RECEIPT.json`; `lean/verify_receipt.py` checks source custody and the no-escape boundary using only Python's standard library.

This does not replay Lean from a clean checkout and does not prove correspondence to the native `LayoutNumerator.entry` definition. Those remain the next obligations.
