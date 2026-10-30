# Evidence

| File | Contents |
|---|---|
| `chipfiring_translation.json` | The live-set conditions in net terms, over chip-firing-shaped nets, at two boxes. |
| `relaxation_boundary.json` | Each structural feature relaxed in turn, counting only newly admitted nets. |
| `generalized_conditions.json` | The usable-transition generalization, still unsound, over three boxes. |
| `allfull_obstruction.json` | Revision 0.2.0: the proved equivalence corroborated inside the increasing class, with the control on the hypothesis outside it. |
| `LEAN_RECEIPT.json` | Toolchain, source hashes, declaration list and observed axiom dependencies of every compiled target. |
| `flow_characterization.json` | Revision 0.3.0: the obstruction condition against the exact semantics, with the fixpoint-versus-existential cross-check and all four ablations. |
| `hardness_reduction.json` | Revision 0.4.0: the CNF reduction checked against the exact semantics and a brute-force oracle, with the input-place bounds. |
| `weighted_flow.json` | Revision 0.5.0: the level-based algorithm against the exact semantics over six weighted boxes, with both step ablations. |
| `single_input.json` | Revision 0.6.0: the downward fixpoint over single-input nets with arbitrary outputs and weights, with certificate replay and both ablations. |
| `backdoor.json` | Revision 0.8.0: the fixed-parameter procedure over general nets, with both literal-family ablations. |
| `reduction_bridge.json` | Revision 0.9.0: the Lean reduction's net compared with `hardness.py`'s, formula by formula, with a mutated-encoding negative control. |
| `free_choice.json` | Revision 0.10.0: the strict free-choice construction against the SAT oracle, with the free-choice, bridge and ablation gates and the checker control. |
| `marked_graph.json` | Revision 0.11.0: the marked-graph procedure against brute force over 20,000 nets, with both ablations and the checker control. |
| `conflict_free.json` | Revision 0.12.0: the conflict-free procedure against brute force over 20,000 nets, three ablations, the input-place hypothesis test, and the one-conflict-place count of the 0.10.0 nets. |
| `inputless.json` | Revision 0.14.0: conflict-free nets with input-less transitions against the SAT oracle, with the bridge, ablation, the 0.12.0 procedure's failures, and the empty-CNF exception. |
| `lean_decider_bridge.json` | Revision 0.15.0: the compiled decider `decidePreserves`, evaluated by Lean on 400 random conflict-free nets, against brute force. |
| `run_checks.json` | Bundled fast subset with content gates. |

Reproduce with
`python -B discoveries/concurrency/capacity-preservation-boundary/verification/run_checks.py`.
The full boxes behind `generalized_conditions.json` take several minutes.
