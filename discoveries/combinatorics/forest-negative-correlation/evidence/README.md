# Evidence

| File | Contents |
|---|---|
| `forest_nc_runs.json` | Run summaries from `fnc.c` and `cnc.c`: graphs, pairs, violations (always 0), smallest normalised margin, per vertex count and multigraph family. |
| `check_forest_nc.json` | Output of `check_forest_nc.py`. |
| `na_scan.json` | Exact negative-association scan at `λ = 1` on 2-connected graphs with 4..6 vertices, up-set pairs on disjoint edge sets of sizes (3,3) and (4,2), both models, and the positive control. |
| `raw/` | The raw run outputs behind every number above: `f3..f8`, `f9r_0`, `f9r_1`, `c3..c8`, `c9r_0`, `c9r_1` (simple graphs, forests and connected subgraphs), `mf6`, `mc6`, `mf7`, `mc7` (multigraph families), `f10.txt` (the 500 residue-class summaries of the 10-vertex forest run, in class order), and `n10_crosschecks.txt` (the two independent confirmations of the 10-vertex totals). The gate `RAW_PROVENANCE` re-derives `forest_nc_runs.json` from these. |
