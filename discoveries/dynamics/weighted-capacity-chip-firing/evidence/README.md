# Evidence

| File | Contents |
|---|---|
| `finite_search_n3.json` | n<=3, multiplicity<=3, sink<=2, capacities at bound and bound+1. Positive control at `C=d`, candidate bound, single-receiver sharpness sweep. |
| `finite_search_n4.json` | n<=4, multiplicity<=2, sink<=1, capacities at the bound. |
| `independent_check_n3.json` | Separately implemented check of the transfer theorem's conclusion, with its adverse control. |
| `characterization_n3.json` | Exactness census of the three live-set conditions against the transfer property, n<=3. |
| `characterization_ablation.json` | Each condition dropped in turn; counts the systems the predicate then gets wrong. |
| `cycle_obstruction_probe.json` | The cycle witness confirmed across cyclic graph and capacity pairs. |
| `wellfounded_equivalence_n3.json` | Revision 0.5.0: the well-foundedness statements checked over the same box by independent methods, with the hypothesis ablation. |
| `sink_collapse_n3.json` | Revision 0.7.0: capped-sink transfer against "no vertex live" at sink capacities 0, 1, 2, 4, with the bridge, witness and cap-not-idle gates. |
| `lean_decider_bridge.json` | Revision 0.11.0: the compiled decider `decideTerminalStable`, evaluated by Lean on 500 census systems, against simulated transfer. |
| `decoder_check.json` | Revision 0.12.0: 80 random instances decoded with kernel-checked verdicts, 42 compared with simulated transfer, plus the wrong-verdict and dropped-arc controls. |
| `run_checks.json` | Output of the bundled checks, including their content gates. |
| `LEAN_RECEIPT.json` | Toolchain, source hashes, declaration list and axiom dependencies of the compiled targets. |

All counts are reproducible from a clean checkout by
`python -B discoveries/dynamics/weighted-capacity-chip-firing/verification/run_checks.py`.
