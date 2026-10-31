# Reference tools

| File | Role |
|---|---|
| `check_forest_nc.py` | Required gate (pure Python, about 10 s). Gates: `DP_EQUALS_BRUTE_FORCE`, `BLOCK_FACTORISATION`, `GRAPH_LIST`, `NC_SMALL`, `SMALL_LAMBDA_LAW`, `NA_SMALL`, `EVIDENCE_SUMMARY`, `RAW_PROVENANCE`. |
| `fnc.c`, `cnc.c` | Exact checkers for forests and connected spanning subgraphs. They read graph6 by default, or `multig -T` text with `-T`; `-v` prints every pair's polynomial. Compile with `-lm`. |
| `fnc4.c` | Faster forest checker, same output format as `fnc.c`; used for the 10-vertex run (about 2x faster than `fnc.c` at 8 vertices, more at 10). Simple graphs only, no multigraph mode. |
| `validate_fnc4.sh` | Requires `fnc4 -v` output to equal `fnc -v` output line for line on every 2-connected graph of the given orders. `./validate_fnc4.sh "4 5 6 7 8"`, about 2 minutes; `GENG=/path/to/geng` if `geng` is not alongside. This is the only thing that licenses using `fnc4.c` for the 10-vertex run. |
| `two_connected_le7.g6` | `geng -C` output for 3..7 vertices (538 graphs), used by the gate. |
| `brute_force_crosscheck.py`, `brute_force_crosscheck_connected.py`, `brute_force_multigraph.py` | Compare the C tools with subset enumeration. They expect `geng`, `multig`, `fnc` and `cnc` in the working directory. |
| `build_evidence.py` | Assembles `evidence/forest_nc_runs.json` from the raw run outputs: `build_evidence.py OUT.json RAWDIR`, with `GENG=` and `MULTIG=` if nauty is not in the working directory. `RAWDIR` is `evidence/raw/`. |
| `small_lambda_graph_check.py` | Checks the small-`λ` law (§4) on all 2-connected graphs with the given vertex counts, comparing `fnc -v` output with an independent enumeration of the cycles through `e` and `f`. |
| `small_lambda_matroid_check.py` | Checks the small-`λ` law on random binary and ternary vector matroids and on uniform matroids. |
| `s8_negative_coefficient_scan.py` | Scans all `[I_4 \| A]` binary matroids for negative Rayleigh coefficients and prints the first example, which has the circuit profile of `S_8`. |
| `na_scan.py` | Exact NA scan: `python3 na_scan.py MODEL K1 K2 n...` with `MODEL` = `Z`, `C`, or the positive control `K`; needs `geng`. |

Build nauty's `geng` and `multig` from the source in the PyPI sdist
`pynauty-2.8.8.1.tar.gz` (`src/nauty2_8_8`: `./configure && make geng multig`).

## Reproducing the large runs

```text
cc -O2 -o fnc fnc.c -lm && cc -O2 -o cnc cnc.c -lm && cc -O3 -o fnc4n fnc4.c -lm
geng -Cq 9 0/2 | ./fnc  >  f9r_0.txt      # and 1/2; forests, 9 vertices
geng -Cq 9 0/2 | ./cnc  >  c9r_0.txt      # and 1/2; connected subgraphs, 9 vertices
geng -Cq 6 | multig -q -T -m3 | ./fnc -T  >  mf6.txt
geng -Cq 7 | multig -q -T -m2 | ./fnc -T  >  mf7.txt
./validate_fnc4.sh "4 5 6 7 8"            # before trusting fnc4n
for r in $(seq 0 499); do                 # forests, 10 vertices, about 8 CPU-hours
  geng -Cq 10 $r/500 | ./fnc4n > chunk_$r.txt
done
cat chunk_{0..499}.txt > f10.txt
```

The raw outputs of all of these are shipped in `evidence/raw/`, and the gate
re-derives every recorded total from them.
