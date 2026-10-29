# Verification

The reference and independent finite implementations are deliberately
separate. `run_checks.py` launches both by path with no repository `PYTHONPATH`,
checks the exact finite box and adverse witnesses, and compares deterministic
result hashes. The Lean project is independently replayed under its pinned
4.35.0 toolchain.
