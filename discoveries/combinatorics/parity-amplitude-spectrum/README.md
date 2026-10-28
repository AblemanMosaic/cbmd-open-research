# Parity-amplitude spectrum

> **Pipeline stage:** `CLAIM_BOUND`  
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`

Permanent discovery ID: `CBMD-COMB-PARITY-AMPLITUDE-001`

## Exact candidate claim

The reference integer amplitude has a coefficient-extraction formula depending only on `(A,R,delta,f)`. On the centered line `delta = 2A+R`, the amplitude vanishes over the integers when `d = R-1-f` is odd and has a binomial closed form when `d` is even.

## Current standing

The retained r6 source package contains a written derivation and finite checks. A separated integer cancellation core now compiles under pinned Lean 4.34.1 with no `sorry`, `admit`, or added `axiom` in that proof boundary. The larger native-transport module also compiles, but its four correspondence theorems remain admitted. The Krawtchouk orthogonality and symmetry ingredients are classical; novelty of the source-specific identification remains unassessed.

## Next obligation

Prove or disprove the proposed `entry_closed_form` against the pinned `entry`, `integerDifference`, `swapPositions`, `mismatches`, and `parityCoefficients` definitions. Only after that correspondence closes may the compiled cancellation core support a native centered-vanishing theorem.

## Nonclaims

No native algorithmic speedup, compiled proof of source transport, literature-wide novelty, or coefficient transport across rings is claimed.
