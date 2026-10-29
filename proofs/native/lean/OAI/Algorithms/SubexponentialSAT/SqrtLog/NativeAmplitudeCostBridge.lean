import OAI.Algorithms.SubexponentialSAT.SqrtLog.CenteredNativeVanishing

/-!
# Executable master-amplitude boundary

This module isolates the remaining native-cost obligation.  The pinned native
`LayoutNumerator.entry` reduces exactly to one scalar amplitude; `masterAlpha`
is a computable integer implementation of the Batch 5 master formula.  No cost
claim is made until the final scalar identity is proved.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- Generalized integral binomial coefficient, executable for every integer
upper argument. -/
def generalizedChoose (n : ℤ) (k : ℕ) : ℤ :=
  Ring.choose n k

/-- Coefficient of `y^k` in `(1-y)^(-A)`, including the `A = 0` convention. -/
def negativeBinomialCoeff (A k : ℕ) : ℤ :=
  ((A + k - 1).choose k : ℤ)

/-- The executable Batch 5 master formula for the normalized amplitude. -/
def masterAlpha (A R δ f : ℕ) : ℤ :=
  let d := R - 1 - f
  (-1 : ℤ) ^ A *
    ∑ k ∈ range (d + 1),
      generalizedChoose ((A : ℤ) + R - δ) k *
        negativeBinomialCoeff A (d - k)

/-- The integer numerator used by the native entry is the normalized master
amplitude scaled by the exact power of two. -/
def masterNumerator (A R δ f : ℕ) : ℤ :=
  2 ^ (R - 1) * masterAlpha A R δ f

/-- The exact source-facing reduction: all orbit, pivot, difference-product,
and powerset mechanics are discharged before the scalar amplitude boundary. -/
theorem entry_eq_sign_mul_centeredAmplitude
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y) :
    entry i t A R u y =
      (-1 : ℤ) ^ ((mismatches i u y).erase t).card *
        centeredAmplitude A R ((mismatches i u y).card - 1)
          ((activeSet i u).card - (mismatches i u y).card) := by
  simpa [centeredAmplitude] using
    entry_closed_form_guarded i t A R u y horbit ht

/-- Once the remaining pure scalar identity is established, the native entry
is definitionally bound to the executable master formula.  The sign belongs
inside this bridge hypothesis: the reference numerator includes the
`(-1)^f` factor already exposed by `entry_closed_form_guarded`. -/
theorem entry_eq_masterNumerator_of_scalar_bridge
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y)
    (hscalar :
      (-1 : ℤ) ^ ((mismatches i u y).card - 1) *
          centeredAmplitude A R ((mismatches i u y).card - 1)
            ((activeSet i u).card - (mismatches i u y).card) =
        masterNumerator A R (activeSet i u).card
          ((mismatches i u y).card - 1)) :
    entry i t A R u y =
      masterNumerator A R (activeSet i u).card
        ((mismatches i u y).card - 1) := by
  have hcard : ((mismatches i u y).erase t).card =
      (mismatches i u y).card - 1 := by
    exact Finset.card_erase_of_mem ht
  rw [entry_eq_sign_mul_centeredAmplitude i t A R u y horbit ht, hcard]
  exact hscalar

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
