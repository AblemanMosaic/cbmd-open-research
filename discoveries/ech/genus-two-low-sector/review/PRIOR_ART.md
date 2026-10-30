# Prior art

A bounded targeted search against the ECH literature, run to address open
question 6 of the dossier README — *whether an existing Floer calculation
already contains the result in other coordinates*.

The answer is **partially, and the part it does not contain is exactly the
dossier's parameter window.** That is a sharper position than this dossier had
before, in both directions: the headline count is not new, and the gap the
dossier is working in is a named, published open hypothesis rather than
unexplored ground.

## What is already computed

**The groups.**

> Jo Nelson and Morgan Weiler, *Embedded contact homology of prequantization
> bundles*, J. Symplectic Geom. 21 (2023), no. 6, 1077–1189.
> <https://arxiv.org/abs/2007.13883> · <https://ar5iv.arxiv.org/html/2007.13883>

Theorem 1.1, equation (1.2): for a prequantization bundle over `(Σ_g, ω)` with
negative Euler class `e`,

```
ECH_*(Y, ξ, Γ)  ≅  ⊕_{d ≥ 0} Λ^{Γ + (−e)d} H_*(Σ_g; Z_2)
```

as `Z_2`-graded `Z_2`-modules, with non-zero summands for `Γ ∈ {0, …, −e−1}`.
This holds for all `g ≥ 0` and all `e < 0`, so it covers this dossier's
`g = 2`, `e = −b`, `b ≥ 3`, `Γ ∈ {1,2}` at the level of the groups. It makes
rigorous the `Z_2`-graded isomorphism in **Farris's 2011 PhD thesis**, adding
the grading, the Morse–Bott direct-limit argument through filtered
`HM` ≅ filtered `ECH`, and the writhe bounds.

Two features matter for this dossier. The coefficients are `Z_2`, and
**orientations are not defined there** — which is directly relevant to open
question 1, since this dossier asserts relative classes, signs and
orientations. And the `U`-map is **not** computed; Conjecture 1.14 only
conjectures it is a chain-level isomorphism in large degree.

**The `U`-map, and the count of sixteen.**

> Guanheng Chen, *Computing the `U` maps on ECH of prequantization bundles*.
> <https://arxiv.org/pdf/2608.16625>

Theorem 1, quoted: *"Let `(Y,λ)` be a prequantization bundle over a symplectic
surface `(Σ, ω_Σ)` with negative Euler number `e`. Assume `e < χ(Σ)`. If
`Γ = 0` or `Γ > 2g − 2`, then we have a (ungraded) `U`-module isomorphism
`ECH(Y,λ,Γ) ≅ ⊕_{i=1}^{2^{2g}} T^+`"*, where `T^+ = Q[U^{−1},U]/U Q[U]`.

At `g = 2` that is **sixteen ungraded `U`-towers**, which is this dossier's
headline structural claim, already published. The hypothesis `e < χ(Σ) = 2−2g`
reads `e ≤ −3` at genus two, matching `e = −b`, `b ≥ 3` exactly.

## Does it contain this result?

**The claim: yes. The parameter window: no, and the gap is precisely this
dossier's.**

Chen's hypothesis is `Γ = 0` **or** `Γ > 2g − 2 = 2`. This dossier's
`Γ ∈ {1, 2}` lies in the excluded interval `0 < Γ ≤ 2g − 2`. For the dossier's
own smallest decisive test, `g = 2` and `e = −3`, the full range is
`Γ ∈ {0, 1, 2}`: Chen covers `Γ = 0`, and `Γ > 2` is empty. So **`Γ ∈ {1,2}`
is literally the uncovered remainder.**

Chen's Remark 1.5 says the restriction is forced by the basis choice — *"If we
choose them arbitrary, then the pairing may not be the direct sum"* — and the
method is `Q`-coefficient only.

So this dossier is not reproducing a published theorem at `Γ ∈ {1,2}`; it is
proposing the extension past the exact hypothesis that the published method
could not remove. That is a materially better position than *already known*,
and a materially worse one than *new phenomenon*.

## Sixteen is the expected number

`2^{2g}` traces to `dim H^*(Sym^n Σ; Q) = 2^{2g}(n − g + 1)` — the exterior
algebra on `H_1(Σ)` — and is not genus-two-specific. It is consistent with
Nelson–Weiler's Corollary 1.13, whose stable rank is `Z_2^{f(g)}` with
`f(g) = 2^{2g−1}` per `Z_2`-parity: eight even plus eight odd. **Sixteen
should be expected, and should not be presented as a discovery.**

## Terminology, and the single highest-value next check

Chen's construction is cap/fill cobordism maps `Φ_m` paired against a fill,
with the pairing inverted to extract `U` — structurally the same shape as this
dossier's `Ψ_0^ε(1 ⊗ F_1^ε(u²ω))` composition. The difference is the one that
matters: Chen's pairing is **block-diagonal by construction**, which is what
the Macdonald basis buys and why the `Γ` hypothesis exists. He has no
triangularity argument.

This dossier's *upper-triangular pairing with one off-diagonal junction,
removed by an integral shear* therefore looks like the analogue of that basis
choice in the regime where the clean basis is unavailable — plausibly the
right move at `0 < Γ ≤ 2g − 2`. No standard name for `PU = Q`, "junction" or
"shear" was found in this literature.

> **The check worth doing next:** compare this dossier's `U`-recurrence at
> `Γ = 0`, `e = −3` against Chen's explicit `U`-map formula (his Lemma 5.11).
> `Γ = 0` is inside Chen's hypothesis, so agreement there would validate the
> algebraic model against a published computation, and disagreement would
> localize an error before any claim is made at `Γ ∈ {1,2}`.

That comparison has **not** been done here.

## Caveats on this search

- Nelson–Weiler Theorem 1.1 and Chen Theorem 1 and Remark 1.5 are quoted from
  fetched text. **Chen's Lemma 5.5 and Lemma 5.11 are reported from the
  introduction's description of them, not from the lemma bodies; the formulas
  themselves are unverified here.**
- Chen's submission date and venue could not be retrieved; the arXiv abstract
  page returned no metadata. The reference should be treated as a preprint of
  unconfirmed status until checked.
- Kronheimer–Mrowka was not fetched directly; the `[KM07, Cor. 35.1.4]`
  citation is as it appears in Nelson–Weiler.
- Nelson–Weiler's promised sequel on Seifert fiber spaces and the
  `U`-map / orbifold Gromov–Witten relation does not appear to have superseded
  Chen.

## Effect on the dossier's open questions

| question | effect |
|---|---|
| 6, prior art in other coordinates | **answered**: the groups are Nelson–Weiler Thm 1.1 for all `Γ`; the `U`-towers are Chen Thm 1 but only for `Γ = 0` or `Γ > 2g−2` |
| 1, cap/fill composition at the asserted classes, signs, orientations | sharpened: Nelson–Weiler is `Z_2` and defines no orientations, so the sign and orientation assertions have no published counterpart to lean on |
| 2–5 | unchanged |

Nothing in this dossier's model is contradicted by the search. Its headline
count is withdrawn as novel, and its working window is identified as a named
published gap.
