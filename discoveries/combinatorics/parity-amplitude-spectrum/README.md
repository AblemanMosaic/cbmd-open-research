# Classical Krawtchouk identification and native vanishing

> **Pipeline stage:** `REVIEW_READY`
>
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `REVISED`

Permanent discovery ID: `CBMD-COMB-PARITY-AMPLITUDE-001`

## Exact candidate claim

The reference integer amplitude has a coefficient-extraction formula depending only on `(A,R,delta,f)`. On the centered line `delta = 2A+R`, the amplitude vanishes over the integers when `d = R-1-f` is odd and has a binomial closed form when `d` is even.

## Current standing

The identification is now named precisely: the amplitude is `2^(R-1)(-1)^A K_d(-A; R-delta)`, the MacWilliams-Sloane binary Krawtchouk polynomial at a **negative argument** and a possibly-negative length. It reduces to classical Krawtchouk **symmetry** -- the generating function and the `q = 2` reflection law, both polynomial identities needing no measure. *Orthogonality is withdrawn*: it sums over `i = 0 ... n` with `n` a non-negative integer and the arguments inside that range, and here the argument is `-A` and the length may be negative, so the measure does not exist. The centered vanishing is the classical root fact that an odd-degree binary Krawtchouk polynomial vanishes at the centre of its reflection symmetry, which on this line the argument hits exactly. See [`review/PRIOR_ART.md`](review/PRIOR_ART.md) and [`revisions/0.8.0-krawtchouk-named.md`](revisions/0.8.0-krawtchouk-named.md). Source-specific novelty remains unassessed. The original native closed-form candidate was refuted at `Q=2,A=0,R=1`, where its two sides are `0` and `-1`. A guarded correction resolves the truncated-natural-subtraction defect, and the retained 134,370-case finite audit includes deliberate sign and active-cardinality mutants.

Local work subsequently completed the no-escape native centered-vanishing and A=0 collapse proofs and derived an explicit parity-coefficient formula. The [dated evidence snapshot](../../../evidence/iterations/bootstrap-2026-10/README.md) retains the original decisions and observations. Release v0.1 now stages the minimal 41-module OAI closure, exact toolchain and dependency pins, source-custody gate, and executable replay under [`proofs/native`](../../../proofs/native/README.md).

## Next obligation

Obtain an independent source-specific derivation and convention audit, together with targeted prior-art assessment. See the [integration roadmap](../../../docs/INTEGRATION_ROADMAP.md).

## Nonclaims

No native algorithmic speedup, external independent verification, literature-wide novelty, or coefficient transport across rings is claimed.
