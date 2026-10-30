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

## Leads for question 6, located but not examined

A short search on the Floer side found two candidate sources. They are
recorded so a successor starts here. **Neither has been read, and neither is
claimed to settle anything.**

- Tomasz Mrowka, Peter Ozsváth, Baozhen Yu, *Seiberg–Witten Monopoles on
  Seifert Fibered Spaces*, <https://arxiv.org/abs/math/9612221>. The abstract
  describes all monopoles on Seifert fibered spaces for a particular metric and
  perturbation, and identifies flow lines with holomorphic data on an
  associated ruled surface. Prequantization bundles over `Σ_2` are Seifert
  fibered. Monopole Floer homology is isomorphic to ECH (Taubes) and to
  Heegaard–Floer homology. This is therefore the most direct candidate for the
  "other route" §2 mentions. Whether it determines the `U`-module structure at
  the torsion classes `Γ ∈ {1, 2}`, with matching orientations and
  coefficients, is exactly what §2 asks and was not checked.
- Stanislav Jabuka and Thomas Mark, *On the Heegaard Floer homology of a
  surface times a circle*, <https://arxiv.org/abs/math/0502328>. This is Euler
  number `0`, not a prequantization bundle (`e < 0`). It is relevant at most for
  technique, including its 2-torsion phenomenon for `g > 2`, which does not
  arise at `g = 2`.

## Caveats

Chen's submission date and venue could not be retrieved. Theorem 1 and
Remark 1.5 are quoted from fetched text; Lemmas 5.5 and 5.11 were not.

## Question 6: the Heegaard–Floer route (0.3.0-candidate)

This section answers question 6 with a **written derivation from published
theorems**. It is not a citation of a published statement. No source found
states the sixteen-tower result at `Γ ∈ {1, 2}`. The claim is narrower: the
result follows from published Floer theory in five steps, each sourced
below. The derivation has not been checked by a specialist. The point of
recording it is so that one can check it step by step.

**Claim.** For `g = 2`, `e = −b` with `b ≥ 3`, and every torsion class `Γ`
(in particular `Γ ∈ {1, 2}`),
`ECH(Y_b, λ, Γ) ≅ ⊕_{i=1}^{16} T^+` as ungraded `U`-modules, over `F_2` or `Q`.
More generally the same holds for genus `g` with `2^{2g}` towers whenever
`b ≥ 2g − 1`. That bound is exactly Chen's hypothesis `e < χ(Σ)`.

**Step 1: ECH is Heegaard–Floer homology, `U` included.** Chen, *Computing the
`U` maps on ECH of prequantization bundles*, §1: "The (hat) Seiberg-Witten
Floer homology, embedded contact homology, (positive) Heegaard Floer homology
are equivalent … as U-modules", proved by Taubes, Kutluhan–Lee–Taubes and
Colin–Ghiggini–Honda. Chen also says that his Theorem 1 "can be obtained
alternatively" from Heegaard–Floer computations (Ozsváth–Szabó [42, Thm 5.6],
Park [43, Thm 4.1.1]). <https://arxiv.org/pdf/2608.16625>. Under this
equivalence, the class `Γ` corresponds to the spin-c structure
`s_ξ + PD(Γ)`. Because `c_1(ξ)` is torsion, torsion `Γ` corresponds to torsion
spin-c structures.

**Step 2: `Y_b` is surgery on the Borromean knot.** The Borromean knot
`B_g ⊂ #^{2g}(S^1 × S^2)` is fibred with fibre `Σ_{g,1}` and trivial monodromy.
So its complement is `Σ_{g,1} × S^1`, the meridian is the `S^1` factor, and the
fibre framing is `∂Σ_{g,1} × pt`. Filling along `n·μ + λ` glues in a solid
torus whose meridian disk caps `∂Σ_{g,1}` with an `n`-fold twist. The result
is the circle bundle over `Σ_g` with Euler number `∓n`; `n = 0` gives
`Σ_g × S^1`. So both orientations of `Y_b` are surgeries on `B_g` (or its
mirror) with coefficient of absolute value `b`. Published form: Gorsky–Liu–Moore,
*Surgery on links of linking number zero and the Heegaard Floer
d-invariant*: the circle bundle with Euler number `n ≠ 0` "can be obtained
from n-framed surgery in #^{2g}S²×S¹ along the 'Borromean knot'".
<https://arxiv.org/abs/1810.10178>. They also label its torsion spin-c
structures by `−|n|/2 ≤ i ≤ |n|/2`.

**Step 3: the knot complex has zero differential.** By Ozsváth–Szabó, as
quoted in *Knot Floer homology of boundary Dehn twists* §2,
`CFK^∞(B_g) = F[U, U^{-1}] ⊗ Λ^* H^1(Σ_g)`, with
`C{i, j} = U^{-i} ⊗ Λ^{g−i+j} H^1(Σ_g)`. <https://arxiv.org/html/2609.13097>.
This is a free complex of rank `2^{2g}` over the principal ideal domain
`F[U, U^{-1}]`. Its homology, `HF^∞` of `#^{2g}(S^1 × S^2)` in the torsion
spin-c structure, is also free of rank `2^{2g}`: `HF^−(#^m(S^2 × S^1)) ≅
Λ^* H^1 ⊗ F[U]` (Ozsváth–Szabó, *Lectures on Heegaard Floer homology*, §2.5,
<https://web.math.princeton.edu/~petero/Lectures.pdf>). Over the fraction
field, the rank of the homology is `2^{2g} − 2·rank ∂`, so `∂ = 0`.

**Step 4: large surgery applies from `2g − 1`.** Ozsváth–Szabó, *Holomorphic
disks and knot invariants*, Theorem 4.1: for an oriented knot `(Y, K)` in an
arbitrary oriented three-manifold with a compatible Seifert surface,
`CF^+(Y_{−p}(K), s)` is computed by a quotient complex `C{max(i, j−s) ≥ 0}` of
`CFK^∞` for `|s| ≤ p/2` and `p ≥ N`. Remark 4.3: "we can take N = 2g − 1,
where g denotes the genus of the knot". <https://arxiv.org/pdf/math/0209056>.
`B_g` has genus `g`, so for `g = 2` this needs `b ≥ 3`, the dossier's own
range. The labels `s` with `|s| ≤ p/2` cover every residue mod `p`, hence
every torsion spin-c structure, including those of `Γ = 1, 2`.

**Step 5: towers only.** With `∂ = 0`, the quotient complex splits over
generators. A generator `x` of Alexander grading `A` contributes `U^{−i}x`
exactly for `i ≥ min(0, s − A)`. That is an up-set of indices, so it
contributes one copy of `T^+`. (The other convention, `min(i, j − s) ≥ 0`,
gives `i ≥ max(0, s − A)`, again one `T^+`.) So
`HF^+(Y_{−b}(B_2), s) ≅ ⊕^{16} T^+` and `HF_red = 0` for every torsion `s`.
`HF_red` and the rank of `HF^∞` are unchanged by reversing orientation, so the
same holds for `−Y_b`. Step 1 then gives the claim.

**What this changes.** The algebraic direct limit of the dossier's recurrence,
sixteen ungraded `U`-towers at `Γ ∈ {1, 2}`, agrees with this derivation, which
is consistent. But the tower count is then not a new invariant: published Floer
theory already determines it. What the derivation does **not** give is the
dossier's actual content:

- the raw cap classes as filtered bases at the specified cutoffs;
- the explicit low-sector `U`-recurrence with its off-diagonal junction;
- the filtered (action-level) information.

Those remain the proposed contribution, and questions 1–5 about them are
untouched.

**Gaps, stated so they can be checked.**
- Step 1 rests on Chen's summary of the ECH = SWF = HF isomorphisms as
  `U`-module isomorphisms. The isomorphism that matches `Γ` to a spin-c
  structure is used, not re-derived.
- Step 3 takes the quoted description of `CFK^∞(B_g)` as a reduced model of
  rank `2^{2g}`. Over `Z`, that requires the integral description cited there
  (Jabuka–Mark, §3.2). Over `F_2` or `Q`, the rank argument suffices once
  `\widehat{HFK}(B_g)` is free of rank `2^{2g}`.
- Step 4 is quoted from the theorem and remark. The `max`/`min` convention
  difference between sources does not affect step 5.
- The surgery description in step 2 is argued here and matches the published
  description quoted above.
- **Not read:** the text of Ozsváth–Szabó, *Knot Floer homology and integer
  surgeries*, AGT 8 (2008), §5 / Theorem 5.6. That is the published
  computation of the reduced Heegaard–Floer homology of non-trivial circle
  bundles over `Z/2`. Every accessible text extraction stops before §5. Read
  it directly: if its formula gives a nonzero `HF_red` for some torsion spin-c
  structure with `|n| ≥ 2g − 1`, step 5 is wrong.

**A second source for steps 3 and 4, over `Z`.** Jabuka–Mark, *The Heegaard
Floer homology of a surface times a circle*
(<https://arxiv.org/html/math/0502328v1>), work with the same knot
`K ⊂ #^{2g}(S^1 × S^2)`, the one whose 0-surgery is `Σ_g × S^1`. Their
equation (13) gives `\widehat{HFK}(Y, K, j, s) ≅ Λ^{g+j} H^1(Σ_g)` for
`j = −g, …, g`, and `HFK^∞ ≅ \widehat{HFK} ⊗ Z[U, U^{−1}]`. Their Theorem 2.1,
the large-surgery isomorphism attributed to Ozsváth–Szabó, holds "for all
n ≥ 2g − 1 where g is the genus of K". This supplies the integral form of
step 3 and the `2g − 1` bound of step 4 for this knot directly.

**Independent check.** A second reader, working from this text without the
dossier, tried to break each step. Steps 1, 2 and 4 were confirmed from
sources (step 4 with the caveat that Remark 4.3 is only sketched). Steps 3
and 5 were re-derived. No error was found. Park's correction terms, as quoted
by Gorsky–Liu–Moore (`d_bot = φ − g`), agree with the zero-differential model;
one parity shift in `d_top` was attributed to how `d_top` is defined and was
not verified. A rank count from the Nelson–Weiler groups, with a grading
formula the reader fitted rather than quoted, gave 8 per degree in the stable
range at `g = 2`, `b = 3`, consistent with 16 towers. Neither check substitutes
for reading Theorem 5.6.
