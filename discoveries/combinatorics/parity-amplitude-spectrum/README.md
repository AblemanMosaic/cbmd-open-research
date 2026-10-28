# Parity-amplitude spectrum

> **Pipeline stage:** `CLAIM_BOUND`  
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`

Permanent discovery ID: `CBMD-COMB-PARITY-AMPLITUDE-001`

## Exact candidate claim

The reference integer amplitude has a coefficient-extraction formula depending only on `(A,R,delta,f)`. On the centered line `delta = 2A+R`, the amplitude vanishes over the integers when `d = R-1-f` is odd and has a binomial closed form when `d` is even.

## Current standing

The retained r6 source package contains a written derivation and finite checks. A separated integer cancellation core compiles under pinned Lean 4.34.1 with no proof escapes. The first proposed native closed form was then disproved directly against the pinned `entry` definition: at `Q=2,A=0,R=1`, its two sides are `0` and `-1`. The defect is truncated natural subtraction in the lower binomial index. The corrected guarded theorem now compiles against that same pinned native `entry`: the proof identifies the unique active subword, evaluates its sign, cancels inactive selected coordinates, applies the exact guarded powerset count, and assembles the outer coefficient sum. The parity-interpolant reflection law also now compiles in a separate no-escape module, using rational-polynomial interpolation uniqueness rather than an admission. The earlier 134,370-case finite audit and two mutant families remain adverse evidence, not a substitute for the proofs. The Krawtchouk ingredients are classical; novelty of the source-specific identification remains unassessed.

## Next obligation

Compose the compiled guarded `entry_closed_form` and compiled parity-reflection theorem into the native centered-vanishing corollary, recording the first exact obstruction if the source-level coefficient transport does not close.

## Nonclaims

No native algorithmic speedup, compiled centered-vanishing source theorem, clean-checkout independent replay, literature-wide novelty, or coefficient transport across rings is claimed.
