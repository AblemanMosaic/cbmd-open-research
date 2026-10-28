# Reference amplitude evaluation and cost model

> **Pipeline stage:** `REVIEW_READY`
>
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`

Permanent discovery ID: `CBMD-ALG-AMPLITUDE-COST-001`

## Exact candidate claim

Under the declared reference cost model, one integer amplitude can be evaluated from the coefficient formula using `O(R)` big-integer arithmetic operations, while the frozen enumeration producer performs exactly `sum_{j<R} C(Q-1,j) 2^j` indicator tests per amplitude call. A table of all `(delta,f)` amplitudes has at most `Q R` entries. Row assembly from that table is admitted only when `2^(R-1)` and every node factor `s+1` used by the product are units.

## Current standing

The corrected r7 source package is sealed, cold-replayed, and represented here by exact source copies. The checkout replay confirms 163,912 closed/enumerated amplitude equalities, 10,476 row equalities, and two adverse unit controls. The 24,685,131 enumeration count at `(Q,R)=(80,5)` is explicitly per amplitude call; a row may invoke the producer once per active pivot.

## Next obligation

Bind the closed route to an executable native entry under an explicit native cost model, or identify the first exact source-level obstruction. Novelty and external mathematical review remain separate obligations.

## Nonclaims

Nothing here is a native SAT speedup, a wall-clock theorem, a total owner-sum cost theorem, or a claim about an executable realization of the pinned noncomputable native entry.

## Reproduce

From the repository root:

```text
python -B discoveries/algorithms/reference-amplitude-cost-model/verification/reference-model/verify.py
```

The source archive itself is retained outside this repository; its detached receipt and exact member hashes are in `evidence/`.
