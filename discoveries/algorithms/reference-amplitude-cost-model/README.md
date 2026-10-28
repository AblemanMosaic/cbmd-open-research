# Reference amplitude evaluation and cost model

> **Pipeline stage:** `CLAIM_BOUND`  
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`

Permanent discovery ID: `CBMD-ALG-AMPLITUDE-COST-001`

## Exact candidate claim

Under the declared reference cost model, one integer amplitude can be evaluated from the coefficient formula using `O(R)` big-integer arithmetic operations, while the frozen enumeration producer performs exactly `sum_{j<R} C(Q-1,j) 2^j` indicator tests per amplitude call. A table of all `(delta,f)` amplitudes has at most `Q R` entries. Row assembly from that table has separate ring-unit hypotheses and is not yet admitted here.

## Current standing

The r6 source package contains executable evidence and written cost arguments, but two statements require correction before public qualification: the 24,685,131 count is per amplitude call rather than per row, and the row-assembly identity requires the inverse of `2^(R-1)` plus the inverses of every node factor used in the product.

## Next obligation

Correct the source documentation and evidence labels, state exact unit hypotheses, add a nonunit-node refusal test, and regenerate the deterministic evidence.

## Nonclaims

Nothing here is a native SAT speedup, a wall-clock theorem, or a claim about an executable realization of the pinned noncomputable native entry.
