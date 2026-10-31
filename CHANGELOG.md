# Changelog

## Unreleased

- Integrated the 19-dossier research portfolio and repaired its reproduction
  boundary: checked Lean runners now resolve `lean.exe` and `lake.exe` through
  `CBMD_LEAN_BIN` on Windows, full qualification installs pinned Python and GAP
  dependencies, and CI separately recompiles all five source-bound discovery
  proof projects.
- Split dependency-free repository qualification from full discovery
  qualification with `--repository-only`. Missing dependencies for required
  checks are a fail-closed error in the full scope. Five Lean-backed checked
  decoder/decider gates that had accidentally remained optional are now
  required, so full qualification cannot report `PASS` when Lean is absent.
  Those runners now resolve the explicit override, the exact Elan 4.35.0
  installation, and only then `PATH`, avoiding an unconfigured Elan proxy when
  their temporary build directory has no `lean-toolchain` file.

- Added the capacity-preservation boundary dossier
  (`CBMD-CON-CAPACITY-PRESERVATION-001`), mapping how far the chip-firing
  characterization reaches in Petri nets with place capacities: exact for
  chip-firing-shaped nets, sound but incomplete under self-feedback, and unsound
  once a place has two consumers or a transition has two inputs.

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
- Resolved cyclic graphs in the negative: a compiled cycle obstruction shows
  preservation fails at every capacity with `C(v) >= d(v)` once a directed cycle
  is present, and a forward ordering provably excludes that structure. The two
  results partition the model.

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
