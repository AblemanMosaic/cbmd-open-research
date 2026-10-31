# Reference tools

All GAP scripts need GAP 4 with the SmallGrp and CTblLib packages (tested:
GAP 4.12.1, SmallGrp 1.5.3, CTblLib 1.3.7; on Ubuntu `apt-get install gap-core gap-libs`).

| File | Role |
|---|---|
| `check_mckay_minimal.py` | Required gate (about 30 s). Runs the GAP scripts below on small parameters and checks the recorded evidence. Fails if GAP is missing. |
| `mckay_scan.g` | Exhaustive scan over SmallGroups: every faithful `γ` into `SL_n` without trivial constituent, `n ≤ DMAX`. Flags `HIT` (`|K| = |G^ab|`, by Gaetz's formula, confirmed by Smith normal form), `MISMATCH` (hit differs from Conjecture 6) and `BELOW` (would contradict BKR). Variables `ORDERS`, `DMAX`, `SKIPAB`, `OUT`. |
| `so3.g` | Proposition 3 and Theorem 4 for cyclic and dihedral groups (`m ≤ MMAX`), `A_4`, `S_4`, `A_5`, built from explicit matrices in `SU(2)` and their symmetric squares. Variables `MMAX`, `OUT`. |
| `prim.g` | The primitive finite subgroups of `SL_3(ℂ)` (Proposition 5). Variable `OUT`. |
| `atlas_scan.g` | Same scan as `mckay_scan.g` on ATLAS character tables. Variables `NAMES`, `DMAX`; prints to stdout. |
| `build_evidence.py` | Builds `evidence/mckay_scans.json` from raw outputs. |

Reproduce the large scans (driver files set the variables, then `Read` the script):

```text
gap -q   # ORDERS := [2..40];; DMAX := 5;; SKIPAB := false;; OUT := "all40.out";; PrintTo(OUT, "");; Read("mckay_scan.g");
gap -q   # ORDERS := Filtered([2..150], x -> x <> 128);; DMAX := 6;; SKIPAB := true;; OUT := "nonab150.out";; PrintTo(OUT, "");; Read("mckay_scan.g");
```
