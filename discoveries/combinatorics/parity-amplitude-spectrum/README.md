# Parity-amplitude spectrum

> **Pipeline stage:** `CLAIM_BOUND`  
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`

Permanent discovery ID: `CBMD-COMB-PARITY-AMPLITUDE-001`

## Exact candidate claim

The reference integer amplitude has a coefficient-extraction formula depending only on `(A,R,delta,f)`. On the centered line `delta = 2A+R`, the amplitude vanishes over the integers when `d = R-1-f` is odd and has a binomial closed form when `d` is even.

## Current standing

The retained r6 source package contains a written derivation and finite checks. A separated integer cancellation core compiles under pinned Lean 4.34.1 with no proof escapes. The first proposed native closed form was then disproved directly against the pinned `entry` definition: at `Q=2,A=0,R=1`, its two sides are `0` and `-1`. The defect is truncated natural subtraction in the lower binomial index. A guarded revision passed 134,370 finite comparisons but is not yet proved. The Krawtchouk ingredients are classical; novelty of the source-specific identification remains unassessed.

## Next obligation

Prove the revised guarded `entry_closed_form` from the pinned `integerDifference`, swap, mismatch, and parity-coefficient definitions. Only after that correspondence closes may the compiled cancellation core support a native centered-vanishing theorem.

## Nonclaims

No native algorithmic speedup, compiled proof of source transport, literature-wide novelty, or coefficient transport across rings is claimed.
