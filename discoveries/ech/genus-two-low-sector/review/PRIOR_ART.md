# Prior-art check

A bounded search against the ECH literature. It **confirms** the literature
section of the dossier's own argument
([§2](../argument/GENUS_TWO_LOW_SECTOR_REVIEW.md#2-relationship-to-the-existing-literature))
from fetched primary text, adds one observation, and **does not** settle open
question 6.

An earlier version of this note, committed as `d249975`, presented these
findings as a correction to the dossier — withdrawing the count of sixteen
`U`-towers as already published and marking question 6 answered. Both were
wrong, and that version was written without first reading §2, which already
contains everything it reported. The record of the error is in
[`docs/CORRECTIONS.md`](../../../../docs/CORRECTIONS.md).

## What the search confirms

**The groups**, for every `Γ`, over `Z_2`:

> Jo Nelson and Morgan Weiler, *Embedded contact homology of prequantization
> bundles*, J. Symplectic Geom. 21 (2023), no. 6, 1077–1189, Theorem 1.1.
> <https://arxiv.org/abs/2007.13883>

`ECH_*(Y, ξ, Γ) ≅ ⊕_{d ≥ 0} Λ^{Γ + (−e)d} H_*(Σ_g; Z_2)` as `Z_2`-graded
`Z_2`-modules, for all `g ≥ 0` and `e < 0`, making rigorous Farris's 2011
thesis. The `U`-map is not computed there. §2 already cites this and notes the
`F_2` coefficients.

**The `U`-towers**, for `Γ = 0` or `Γ > 2g − 2` only:

> Guanheng Chen, *Computing the `U` maps on ECH of prequantization bundles*,
> Theorem 1 and Remark 1.5. <https://arxiv.org/pdf/2608.16625>

For `e < χ(Σ)`, `ECH(Y, λ, Γ) ≅ ⊕_{i=1}^{2^{2g}} T^+` as ungraded `U`-modules
when `Γ = 0` or `Γ > 2g − 2`; Remark 1.5 attributes the restriction to the basis
choice. At genus two the excluded classes are exactly `Γ ∈ {1, 2}`. §2 already
says precisely this, and frames the dossier as the proposed extension to those
two classes.

So the count of **sixteen** `U`-towers is the *expected* count, `2^{2g}` — but
at `Γ ∈ {1, 2}` it is **not** published. It is this dossier's proposed result.
The earlier version of this note had that backwards.

## The one observation the search adds

Nelson–Weiler work over `Z_2` and **do not define orientations**. The dossier
asserts relative classes, signs and orientations at the unstable initial
sector (open question 1), and its rational application follows the
formal-properties argument discussed by Chen. The `Z_2` framework therefore
supplies no sign or orientation information to lean on in that sector. This is
a small sharpening of question 1, not a new obstruction.

## What the search did not do

**Open question 6 is about a different route.** §2 records that Chen
identifies existing **Heegaard–Floer** computations and equivalences as another
route to his stated theorem, and asks whether such a computation already proves
the sixteen-tower statement at the two excluded classes — matched in torsion
class, spin-c structure, orientation, coefficient field and Floer flavour. This
search looked only at ECH sources. It did not examine Heegaard–Floer
computations for circle bundles over genus-two surfaces, so question 6 remains
open exactly as stated.

**The bulk-recurrence agreement is asserted, not checked here.** §2 states
that Chen's bulk recurrence agrees, after genus-two specialization, with the
dossier's stable-sector formula. No machine check of that agreement is present
in `verification/`, and this search did not obtain the body of Chen's
Lemma 5.11 — only his introduction's description of it — so it could not
supply one.

## Caveats

Chen's submission date and venue could not be retrieved. Theorem 1 and
Remark 1.5 are quoted from fetched text; Lemmas 5.5 and 5.11 were not.
