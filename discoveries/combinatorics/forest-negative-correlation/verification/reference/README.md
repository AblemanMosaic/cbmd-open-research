# Reference tools

| File | Role |
|---|---|
| `check_forest_nc.py` | Required gate (pure Python, about 10 s). |
| `fnc.c`, `cnc.c` | Exact checkers for forests and connected spanning subgraphs. They read graph6 by default, or `multig -T` text with `-T`; `-v` prints every pair's polynomial. |
| `two_connected_le7.g6` | `geng -C` output for 3..7 vertices (538 graphs), used by the gate. |
| `brute_force_crosscheck.py`, `brute_force_crosscheck_connected.py`, `brute_force_multigraph.py` | Compare the C tools with subset enumeration. They expect `geng`, `multig`, `fnc` and `cnc` in the working directory. |
| `build_evidence.py` | Assembles `evidence/forest_nc_runs.json` from the run outputs. |

Build nauty's `geng` and `multig` from the source in the PyPI sdist
`pynauty-2.8.8.1.tar.gz` (`src/nauty2_8_8`: `./configure && make geng multig`).
