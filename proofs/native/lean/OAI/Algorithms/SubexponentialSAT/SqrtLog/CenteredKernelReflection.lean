import OAI.Algorithms.SubexponentialSAT.SqrtLog.ParityReflection
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Coefficient reversal for the centered kernel

This module proves the second symmetry needed for native centered vanishing.
The polynomial `(X - 1)^f (X + 1)^m` is reciprocal up to the sign
`(-1)^f`; consequently its coefficients reverse with that sign.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Polynomial

noncomputable section

theorem reflect_X_sub_one_pow (n : ℕ) :
    reflect n ((X - 1 : ℤ[X]) ^ n) =
      C ((-1 : ℤ) ^ n) * (X - 1 : ℤ[X]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, show n + 1 = n + 1 by rfl,
        reflect_mul ((X - 1 : ℤ[X]) ^ n) (X - 1)
          (by simpa using natDegree_pow_le_of_le n (natDegree_X_sub_C_le (1 : ℤ)))
          (natDegree_X_sub_C_le (1 : ℤ)), ih]
      have hlinear : reflect 1 (X - 1 : ℤ[X]) = -(X - 1) := by
        rw [reflect_sub, reflect_one_X, reflect_one]
        ring
      rw [hlinear]
      ring_nf
      rw [C_neg]
      ring

theorem reflect_X_add_one_pow (n : ℕ) :
    reflect n ((X + 1 : ℤ[X]) ^ n) = (X + 1 : ℤ[X]) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, show n + 1 = n + 1 by rfl,
        reflect_mul ((X + 1 : ℤ[X]) ^ n) (X + 1)
          (by simpa using (natDegree_pow_X_add_C (R := ℤ) n 1).le)
          (by simpa using (natDegree_pow_X_add_C (R := ℤ) 1 1).le), ih]
      have hlinear : reflect 1 (X + 1 : ℤ[X]) = X + 1 := by
        rw [reflect_add, reflect_one_X, reflect_one]
        ring
      rw [hlinear]

/-- The centered kernel used by the umbral form. -/
def centeredKernel (f m : ℕ) : ℤ[X] :=
  (X - 1) ^ f * (X + 1) ^ m

theorem reflect_centeredKernel (f m : ℕ) :
    reflect (f + m) (centeredKernel f m) =
      C ((-1 : ℤ) ^ f) * centeredKernel f m := by
  rw [centeredKernel,
    reflect_mul ((X - 1 : ℤ[X]) ^ f) ((X + 1 : ℤ[X]) ^ m)
      (by simpa using natDegree_pow_le_of_le f (natDegree_X_sub_C_le (1 : ℤ)))
      (by simpa using (natDegree_pow_X_add_C (R := ℤ) m 1).le),
    reflect_X_sub_one_pow, reflect_X_add_one_pow]
  ring

theorem centeredKernel_coeff_reflect (f m i : ℕ) (hi : i ≤ f + m) :
    (centeredKernel f m).coeff (f + m - i) =
      (-1 : ℤ) ^ f * (centeredKernel f m).coeff i := by
  have h := congrArg (fun p : ℤ[X] => p.coeff i) (reflect_centeredKernel f m)
  rw [coeff_reflect, revAt_le hi, coeff_C_mul] at h
  exact h

end


end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
