import OAI.Algorithms.SubexponentialSAT.SqrtLog.GeneralizedChooseLinear

/-!
# Recurrence-realized master numerator

This is the first fully executable value route whose generalized coefficients
are proved to use the exact-division recurrence from BCM-1.  The definition
below intentionally does not yet claim the optimal shared operation count:
each coefficient call is structurally recursive and may be recomputed.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- Master amplitude with both binomial factors realized by the proved linear
exact-division recurrence. -/
def masterAlphaLinear (A R δ f : ℕ) : ℤ :=
  let d := R - 1 - f
  (-1 : ℤ) ^ A *
    ∑ k ∈ range (d + 1),
      generalizedChooseLinear
          ((A : ℤ) + (R : ℤ) - (δ : ℤ)) k *
        negativeBinomialLinear A (d - k)

def masterNumeratorLinear (A R δ f : ℕ) : ℤ :=
  2 ^ (R - 1) * masterAlphaLinear A R δ f

theorem masterAlphaLinear_eq_masterAlpha (A R δ f : ℕ) :
    masterAlphaLinear A R δ f = masterAlpha A R δ f := by
  simp only [masterAlphaLinear, masterAlpha]
  apply congrArg ((-1 : ℤ) ^ A * ·)
  apply Finset.sum_congr rfl
  intro k hk
  rw [generalizedChooseLinear_eq_ringChoose,
    negativeBinomialLinear_eq,
    generalizedChoose_eq_ringChoose]

theorem masterNumeratorLinear_eq_masterNumerator (A R δ f : ℕ) :
    masterNumeratorLinear A R δ f = masterNumerator A R δ f := by
  rw [masterNumeratorLinear, masterNumerator,
    masterAlphaLinear_eq_masterAlpha]

/-- Source-level native entry bound to the recurrence-realized executable
value route.  No cost statement is attached here. -/
theorem entry_eq_masterNumeratorLinear
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y)
    (hMleR : (mismatches i u y).card ≤ R) :
    entry i t A R u y =
      masterNumeratorLinear A R (activeSet i u).card
        ((mismatches i u y).card - 1) := by
  rw [masterNumeratorLinear_eq_masterNumerator]
  exact entry_eq_masterNumerator i t A R u y horbit ht hMleR

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
