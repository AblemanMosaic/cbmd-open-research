# Changelog

## Unreleased

- Added the weighted-transfer capacity-blocked chip-firing dossier
  (`CBMD-DYN-WEIGHTED-CAPACITY-001`), resolving the named open successor of the
  finite-capacity result with a compiled Lean 4.35.0 transfer theorem, exact
  enumeration at the bound, a separately implemented conclusion check, and a
  sharpness sweep.
- Recorded that confluence and transfer are not equivalent for capacity-blocked
  systems: the smallest failure at `C(v) = d(v)` is confluent with a single
  wrong normal form, so confluence-only searches understate failure by roughly
  fifty times in the sampled boxes.
- Added a Lean receipt that records actual `#print axioms` output rather than a
  manifest-level allowlist.

- Added the review-ready finite-capacity chip-firing dossier with a concrete
  Lean 4.35.0 theorem, independently reproduced 420,840-state finite box, and
  sharp cyclic and parallel-transfer adverse witnesses.
- Added an isolated finite-dynamics formal replay job and exact source custody
  bound to local commit `6162015` and qualification Q10.
- Preserved the failed Q8 import-path qualification and its Q9/Q10 repair.

## 0.1.0 — 2026-10-28

- Added the portable, disabled-by-default CBMD governed operation harness with exact intent/terminal custody, recovery states, claim ceilings, and 37 required tests.
- Added a standalone standard-library reference evaluator and three independently structured exact oracles, with 12 tests, 37,000+ finite comparisons across the reported case classes, and nine retained adverse mutations.
- Added the minimal native Lean proof envelope: 41 transitive source modules, nine target modules, pinned Lean 4.34.1 and mathlib, exact source custody, and an executable logical-dependency audit.
- Added a portable Lean replay driver and a dedicated public CI replay job.
- Preserved the discovery dossiers, corrections, nonclaims, unresolved ECH transport question, and whole-cost/novelty boundaries.
- Added deterministic release packaging and v0.1 documentation.
