# Reference amplitude cost model (no native speedup claim)

> **Pipeline stage:** `REVIEW_READY`
>
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`

Permanent discovery ID: `CBMD-ALG-AMPLITUDE-COST-001`

## Exact candidate claim

Under the declared reference cost model, one integer amplitude can be evaluated from the coefficient formula using `O(R)` big-integer arithmetic operations, while the frozen enumeration producer performs exactly `sum_{j<R} C(Q-1,j) 2^j` indicator tests per amplitude call. A table of all `(delta,f)` amplitudes has at most `Q R` entries. Row assembly from that table is admitted only when `2^(R-1)` and every node factor `s+1` used by the product are units.

## Current standing

The corrected r7 source package is sealed, cold-replayed, and represented here by exact source copies. The checkout replay confirms 163,912 closed/enumerated amplitude equalities, 10,476 row equalities, and two adverse unit controls. The 24,685,131 enumeration count at `(Q,R)=(80,5)` is explicitly per amplitude call; a row may invoke the producer once per active pivot.

The archived cost write-up's phrase "exponentially cheaper in Q" needs a parameter qualification: at fixed R, the enumeration count is polynomial in Q. The [scope correction](revisions/0.3.0-scope-and-parameter-regime.md) controls the current interpretation while preserving the exact archived source bytes.

## The master formula, derived here (revision 0.4.0-candidate)

The closed route rests on B5-M7, whose proof was held only in the sealed
archive. [`argument/M7_DERIVATION.md`](argument/M7_DERIVATION.md) now proves it
from the producer's definition:
- an indicator collapse shows the amplitude depends only on `(|D|, |E|−1)`;
- an inner sum collapses;
- the parity coefficients have a closed form;
- a change of variables `x = z/(1+z)` finishes it.

A standalone checker verifies each step with code written from the definitions,
and two mutated statements fail as required. It is separately written, not
externally authored.

## Next obligation

Review the reference cost model and explicit parameter regimes. Later local work established source correspondence and a candidate executable joint realization; that [successor line](../native-joint-realization/README.md) is tracked separately with full checkout replay still pending. This reference-only checker does not evaluate that transport.

## Nonclaims

Nothing here is a native SAT speedup, a wall-clock theorem, a total owner-sum cost theorem, or a claim about an executable realization of the pinned noncomputable native entry.

## Reproduce

From the repository root:

```text
python -B discoveries/algorithms/reference-amplitude-cost-model/verification/reference-model/verify.py
```

The source archive itself is retained outside this repository; its detached receipt and exact member hashes are in `evidence/`.

## Neutral and negative results

Three outcomes of this line are neutral or negative and are stated explicitly in
[`argument/NEUTRAL_RESULTS.md`](argument/NEUTRAL_RESULTS.md): the row-assembly
identity is exact but arithmetically neutral, the amplitude table is where the
saving actually lies, and row-centric evaluation loses to the owner-centric
route by orders of magnitude at realistic sizes. They are published so the
rejected ideas are not rebuilt.
