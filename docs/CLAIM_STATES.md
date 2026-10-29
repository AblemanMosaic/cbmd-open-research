# Claim states

The following vocabulary is repository-controlled. A discovery may carry several compatible states.

| State | Meaning |
|---|---|
| `CONJECTURE` | A precise mathematical proposal without a completed written argument. |
| `PROVISIONAL_WRITTEN_ARGUMENT` | A complete-seeming argument is available for criticism but has not received specialist certification. |
| `SOURCE_BOUND_COMPILED` | The stated theorem compiles against the declared concrete formal model and pinned toolchain without admitted proof escapes; external input decoding and novelty remain separate obligations. |
| `EXACT_MODEL_VERIFIED` | Declared algebraic or finite computations passed their stated exact checks. |
| `GEOMETRIC_TRANSPORT_UNRESOLVED` | The link from the verified model to the intended geometric theory remains open. |
| `INDEPENDENTLY_REPRODUCED` | A separately implemented reproduction has been recorded with its scope. |
| `SPECIALIST_REVIEWED` | A specialist review and its bounded conclusion are recorded with permission to identify the reviewer. |
| `REVISED` | The current statement corrects or narrows an earlier public statement. |
| `REFUTED` | A counterexample or invalid inference defeats the stated claim. |
| `SUPERSEDED` | A successor replaces this version without implying that the predecessor was false. |

States are not a linear maturity score. For example, a result can be both `EXACT_MODEL_VERIFIED` and `GEOMETRIC_TRANSPORT_UNRESOLVED`.
