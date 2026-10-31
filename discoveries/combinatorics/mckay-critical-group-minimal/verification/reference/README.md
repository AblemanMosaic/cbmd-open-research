# Reference tools

All GAP scripts need GAP 4 with the SmallGrp and CTblLib packages (tested:
GAP 4.12.1, SmallGrp 1.5.3, CTblLib 1.3.7; on Ubuntu `apt-get install gap-core gap-libs`).

| File | Role |
|---|---|
| `check_mckay_minimal.py` | Required gate (about 1–2 min). Runs the GAP scripts below on small parameters and checks the recorded evidence. Fails if GAP is missing. |
| `mckay_scan.g` | Exhaustive scan over SmallGroups: every faithful `γ` into `SL_n` without trivial constituent, `n ≤ DMAX`. Flags `HIT` (`|K| = |G^ab|`, by Gaetz's formula, confirmed by Smith normal form), `MISMATCH` (hit differs from Conjecture 6) and `BELOW` (would contradict BKR). Variables `ORDERS`, `DMAX`, `SKIPAB`, `OUT`. |
| `so3.g` | Proposition 3 and Theorem 4 for cyclic and dihedral groups (`m ≤ MMAX`), `A_4`, `S_4`, `A_5`, built from explicit matrices in `SU(2)` and their symmetric squares. Variables `MMAX`, `OUT`. |
| `prim.g` | The primitive finite subgroups of `SL_3(ℂ)` (Proposition 5). Variable `OUT`. |
| `atlas_scan.g` | Same scan as `mckay_scan.g` on ATLAS character tables. Variables `NAMES`, `DMAX`; prints to stdout. |
| `sector_check.py` | Numerical check of the edge inequality behind the sector lemma (Lemma 2), `n ≤ 10`. |
| `monotonicity_search.g` | Exhaustive search for violations of `|K(γ_1 ⊕ γ_2)| > |K(γ_1)|`. Variables `ORDMAX`, `D1`, `D2`. |
| `arborescence_check.g` | Lemma A, Proposition B and Theorem M, exactly: the arborescence formula for `det C(γ)`, the `δ_v²` ratio between the counts at different roots, the order formula, the non-negative row expansion, and the strictness witness. Variables `ORDMAX`, `LMAX` (cap on the number of conjugacy classes), `DEG`, `OUT`. About 2 minutes at 24 / 6 / 4; this is the `ARBORESCENCE` gate. |
| `mono2.g` | Theorem M end to end with **no determinant condition** on either summand, abelian groups included, separating the equality cases (`γ_2` a multiple of the trivial character) from the strict ones. Variables `ORDMAX`, `LMAX`, `D1`, `D2`, `OUT`. |
| `super.g` | Corollary M2 (superadditivity) for pairs and triples of faithful summands. Variables `ORDMAX`, `LMAX`, `DEG`, `TRIPLEMAX`, `OUT`. Writes one `PROGRESS` line per group, so a truncated run still has usable output. |
| `bounds_check.py` | Recomputes the finite regions left by the analytic inequalities of Theorems 7 and 8 (pure Python, about 1 s). |
| `monomial_enum.py` | Exact enumeration of the monomial (types C, D) subgroups of `SL_3(ℂ)` in normal form with diagonal part of order `≤ NMAX`; classes, `|G^{ab}|` and Gaetz's product (mpmath). `python3 monomial_enum.py 76 out.jsonl`, about 25 s. |
| `monomial_gap_crosscheck.py` | Rebuilds the enumerated groups as GAP matrix groups and recomputes `|G|`, the product and `|G^{ab}|`. |
| `typeB_exceptional.g` | The 18 reducible (type B) groups with projective image `A_4`, `S_4`, `A_5` and centre of order 2, 4, 6. Variable `OUT`. |
| `build_evidence.py` | Builds `evidence/mckay_scans.json` from raw outputs. |

Reproduce the large scans (driver files set the variables, then `Read` the script):

```text
gap -q   # ORDERS := [2..40];; DMAX := 5;; SKIPAB := false;; OUT := "all40.out";; PrintTo(OUT, "");; Read("mckay_scan.g");
gap -q   # ORDERS := Filtered([2..150], x -> x <> 128);; DMAX := 6;; SKIPAB := true;; OUT := "nonab150.out";; PrintTo(OUT, "");; Read("mckay_scan.g");
gap -q   # ORDMAX := 24;; LMAX := 6;; DEG := 4;; OUT := "arb.out";; PrintTo(OUT, "");; Read("arborescence_check.g");
gap -q   # ORDMAX := 48;; LMAX := 8;; D1 := 4;; D2 := 3;; OUT := "mono2.out";; PrintTo(OUT, "");; Read("mono2.g");
gap -q   # ORDMAX := 48;; LMAX := 9;; DEG := 5;; TRIPLEMAX := 25;; OUT := "super.out";; PrintTo(OUT, "");; Read("super.g");
```
