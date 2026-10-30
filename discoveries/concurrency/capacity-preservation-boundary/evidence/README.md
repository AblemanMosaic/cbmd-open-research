# Evidence

| File | Contents |
|---|---|
| `chipfiring_translation.json` | The live-set conditions in net terms, over chip-firing-shaped nets, at two boxes. |
| `relaxation_boundary.json` | Each structural feature relaxed in turn, counting only newly admitted nets. |
| `generalized_conditions.json` | The usable-transition generalization, still unsound, over three boxes. |
| `allfull_obstruction.json` | Revision 0.2.0: the proved equivalence corroborated inside the increasing class, with the control on the hypothesis outside it. |
| `LEAN_RECEIPT.json` | Toolchain, source hashes, declaration list and observed axiom dependencies for the all-full obstruction. |
| `run_checks.json` | Bundled fast subset with content gates. |

Reproduce with
`python -B discoveries/concurrency/capacity-preservation-boundary/verification/run_checks.py`.
The full boxes behind `generalized_conditions.json` take several minutes.
