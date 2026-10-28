# Second-reader audit of the genus-two low-sector grid

> **Standing:** exact finite audit of the implemented algebraic model; not an independent derivation and not geometric ECH certification.

## Findings

### 1. The single off-diagonal block is structural in the model

The extended scan uses (b\in\{3,4,5,6,7,8,10,12\}), \(\Gamma\in\{1,2\}\), and depth (D=6). In all sixteen cases the only nonzero off-diagonal block is (P_{0,1}), and it has exactly eight nonzero entries.

There is also a direct degree explanation. Write (s=d-m\ge1). For (s\ge2), the required pairing index exceeds the largest available degree. For (s=1) with (m\ge1), the stable basis bounds the largest product degree two below the required index. Only (s=1,m=0) uses the unstable initial bases (B_1,B_2), where the needed degree is reachable. Thus the junction is a feature of the unstable initial presentation, not a generic coupling between every consecutive pair of sectors.

### 2. The adverse control has concentrated distinguishing power

For every audited case with (3\le b\le8), \(\Gamma\in\{1,2\}\), and (1\le D\le3), deleting the junction while leaving the other data unchanged is detected by exactly fifteen sector-one sources. The identity pattern is stable throughout this finite grid, with the (u)-exponents shifting with (b).

Consequently, most columns in the larger verification grid do not distinguish the valid operator from this particular invalid deletion. They still test the within-sector recurrence and normal-form reduction. The evidence is nonvacuous, but its junction-sensitive content is concentrated in a small, fully enumerable source set.

This audit does not claim a universal fifteen-source theorem outside the audited parameter range.

### 3. The recurrence junction is exercised

The number of sources with a lower-sector term is seven for \(\Gamma=1,d=1\), and sixteen for \(\Gamma=2,d=1\) or every (d\ge2) in the audited range. Both the raw and coordinated routes have zero residual mismatches in every case.

### 4. Gram inverses remain integral in the extended check

The exact model produces an integer Gram inverse for every (1\le n\le26). This is consistent with the written unimodularity argument but is not, by itself, a proof for all (n).

## What this changes

The audit strengthens the description of the existing evidence. It does not change the public claim state. In particular, it does not establish the cap/fill formula, continuation comparison, orientation conventions, absolute grading, coefficient transport, or novelty.

## Reproduction

`grid_audit.js` recomputes the extended block scan, junction exercise, adverse control, and Gram-inverse checks using the exact public model core. `distinguishing_sources.js` enumerates representative fifteen-source sets. The pinned result is `grid_audit.json`.
