# Evidence

| File | Contents |
|---|---|
| `finite_search_n3.json` | n<=3, multiplicity<=3, sink<=2, capacities at bound and bound+1. Positive control at `C=d`, candidate bound, single-receiver sharpness sweep. |
| `finite_search_n4.json` | n<=4, multiplicity<=2, sink<=1, capacities at the bound. |
| `independent_check_n3.json` | Separately implemented check of the transfer theorem's conclusion, with its adverse control. |
| `LEAN_RECEIPT.json` | Toolchain, source hashes, declaration list and axiom dependencies of the compiled targets. |

All counts are reproducible from a clean checkout by
`python -B discoveries/dynamics/weighted-capacity-chip-firing/verification/run_checks.py`.
