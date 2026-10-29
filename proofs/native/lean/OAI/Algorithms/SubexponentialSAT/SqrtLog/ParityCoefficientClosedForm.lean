import OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerTranslationMatrix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

/-!
# Closed form for the native parity coefficients

The native upper triangular system is inverted by the integer translation
matrix at shift `-A`.  This gives a source-bound finite closed form for every
coefficient, without solving a fresh interpolation problem.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Matrix Finset
open SubexponentialSAT.BinomialInterpolation

theorem integerTranslation_nat_eq_upper (A R : ℕ) :
    integerTranslation (A : ℤ) R =
      SubexponentialSAT.BinomialMatrix.U ℤ A R := by
  ext i j
  simp only [integerTranslation_apply,
    SubexponentialSAT.BinomialMatrix.U_apply]
  by_cases hij : i.val ≤ j.val
  · rw [if_pos hij, if_pos hij, Ring.choose_natCast]
  · rw [if_neg hij, if_neg hij]

theorem parityCoefficients_eq_integerTranslation_mulVec (A R : ℕ) :
    parityCoefficients (K := ℤ) A R =
      integerTranslation (-(A : ℤ)) R *ᵥ
        (fun j : Fin R => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val) := by
  let c := parityCoefficients (K := ℤ) A R
  let g : Fin R → ℤ := fun j => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val
  have hupper : integerTranslation (A : ℤ) R *ᵥ c = g := by
    rw [integerTranslation_nat_eq_upper]
    exact SqrtLog.LayoutCoefficientBounds.upper_mulVec_parity A R
  calc
    parityCoefficients (K := ℤ) A R = c := rfl
    _ = (1 : Matrix (Fin R) (Fin R) ℤ) *ᵥ c := by simp
    _ = (integerTranslation (-(A : ℤ)) R *
          integerTranslation (A : ℤ) R) *ᵥ c := by
            rw [integerTranslation_neg_mul]
    _ = integerTranslation (-(A : ℤ)) R *ᵥ
          (integerTranslation (A : ℤ) R *ᵥ c) := by
            rw [Matrix.mulVec_mulVec]
    _ = integerTranslation (-(A : ℤ)) R *ᵥ g := by rw [hupper]
    _ = integerTranslation (-(A : ℤ)) R *ᵥ
          (fun j : Fin R => (-1 : ℤ) ^ A * (-2 : ℤ) ^ j.val) := rfl

theorem parityCoefficient_closed_form (A R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) A R j =
      ∑ k : Fin R,
        if j.val ≤ k.val then
          Ring.choose (-(A : ℤ)) (k.val - j.val) *
            ((-1 : ℤ) ^ A * (-2 : ℤ) ^ k.val)
        else 0 := by
  have h := congrFun (parityCoefficients_eq_integerTranslation_mulVec A R) j
  simpa only [Matrix.mulVec, dotProduct, integerTranslation_apply,
    ite_mul, zero_mul] using h

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
