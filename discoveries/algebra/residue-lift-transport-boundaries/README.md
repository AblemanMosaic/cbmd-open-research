# Residue and lift transport boundaries

> **Pipeline stage:** `QUALIFYING`  
> **Claim standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`, `REVISED`

Permanent discovery ID: `CBMD-ALG-RESIDUE-LIFT-001`

## Exact candidate claim

In the retained selected-degree-six source fixture, the correction has residue order two but lifted order one for every compatible exponent `mu >= 2`; a residue-only activity or weight certificate therefore loses a nonzero linear term. In the reference amplitude spectrum, many classes are zero modulo three while nonzero over the integers, so ring, precision, nodes, amplitude, and source identity must be bound before transporting a zero certificate.

## Current standing

The amplitude-spectrum half of the standing obligation is now extracted as a
standalone verifier ([`argument/SEPARATION.md`](argument/SEPARATION.md),
[`verification/separation.py`](verification/separation.py)). The smallest
off-diagonal separation is `A=0, R=2, delta=5, f=0` with amplitude `-6`: zero in
`Z/3`, nonzero in `Z` and `Z/9`. At `(A,R,Q) = (17,5,80)`, 120 of 385 classes are
residue-zero while only 2 are genuinely zero.

A positive control fixes the valuation on the central line by Kummer's theorem,
and a **recorded negative** closes the obvious route: off that line `v_3` is not
a function of the low base-three digits at depth 2 or 3.

The inherited selected-degree-six source fixture is still not reproduced.

## Next obligation

Extract and independently replay the inherited degree-six fixture at residue and
two lifted precisions, binding every ring, node, centre, amplitude and
source-row parameter; and settle whether a full-digit criterion exists off the
central line.

## Nonclaims

No fault in the upstream solver, full produced-leaf realization, native SAT consequence, or novelty determination is claimed.
