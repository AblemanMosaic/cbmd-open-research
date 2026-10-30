# Evidence

| File | Contents |
|---|---|
| `chipfiring_translation.json` | The live-set conditions in net terms, over chip-firing-shaped nets, at two boxes. |
| `relaxation_boundary.json` | Each structural feature relaxed in turn, counting only newly admitted nets. |
| `generalized_conditions.json` | The usable-transition generalization, still unsound, over three boxes. |
| `run_checks.json` | Bundled fast subset with content gates. |

Reproduce with
`python -B discoveries/concurrency/capacity-preservation-boundary/verification/run_checks.py`.
The full boxes behind `generalized_conditions.json` take several minutes.
