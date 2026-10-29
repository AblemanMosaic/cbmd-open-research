import OAI.Algorithms.SubexponentialSAT.SqrtLog.CenteredCancellation
import Mathlib.Algebra.Polynomial.Taylor

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset Polynomial
open SubexponentialSAT.BinomialInterpolation
noncomputable section

/-- Translating the centered kernel to the Taylor coordinate at `1` exposes
the guarded binomial coefficient occurring in the native closed form. -/
theorem taylor_centeredKernel (f m : ℕ) :
    taylor (1 : ℤ) (centeredKernel f m) =
      X ^ f * (X + 2) ^ m := by
  simp only [taylor_apply, centeredKernel, mul_comp, pow_comp, sub_comp,
    add_comp, X_comp, one_comp, C_1]
  ring

theorem taylor_centeredKernel_coeff (f m j : ℕ) :
    (taylor (1 : ℤ) (centeredKernel f m)).coeff j =
      if f ≤ j then
        (2 : ℤ) ^ (m - (j - f)) * (m.choose (j - f) : ℤ)
      else 0 := by
  rw [taylor_centeredKernel, coeff_X_pow_mul']
  by_cases hfj : f ≤ j
  · simp only [if_pos hfj]
    simpa using coeff_X_add_C_pow (R := ℤ) (2 : ℤ) m (j - f)
  · simp only [if_neg hfj]

/-- The `j`th Taylor coefficient at `1` is the binomial moment of the
ordinary coefficients. -/
theorem sum_choose_mul_coeff_eq_taylor_coeff
    (p : ℤ[X]) (N j : ℕ) (hdeg : p.natDegree ≤ N) :
    (∑ i ∈ range (N + 1), (i.choose j : ℤ) * p.coeff i) =
      (taylor (1 : ℤ) p).coeff j := by
  rw [taylor_coeff, hasseDeriv_apply, eval_sum]
  simp only [eval_monomial, one_pow, mul_one]
  rw [p.sum_over_range'
      (f := fun i r => (i.choose j : ℤ) * r)
      (fun _ => mul_zero _) (N + 1) (Nat.lt_succ_of_le hdeg)]

theorem natDegree_centeredKernel_le (f m : ℕ) :
    (centeredKernel f m).natDegree ≤ f + m := by
  refine natDegree_mul_le.trans ?_
  exact Nat.add_le_add
    (by simpa using natDegree_pow_le_of_le f (natDegree_X_sub_C_le (1 : ℤ)))
    (by simpa using (natDegree_pow_X_add_C (R := ℤ) m 1).le)

/-- Expanding the parity interpolant in the binomial basis turns its umbral
pairing with a polynomial into the parity coefficients paired with the Taylor
coefficients at `1`. -/
theorem parity_umbral_eq_sum_taylor (A R f m : ℕ) :
    (∑ i ∈ range (f + m + 1),
        parityInterpolantCore A R i * (centeredKernel f m).coeff i) =
      ∑ j : Fin R,
        parityCoefficients (K := ℤ) A R j *
          (taylor (1 : ℤ) (centeredKernel f m)).coeff j.val := by
  unfold parityInterpolantCore
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_choose_mul_coeff_eq_taylor_coeff
    (centeredKernel f m) (f + m) j.val (natDegree_centeredKernel_le f m)

/-- The guarded integer amplitude from the native entry closed form. -/
def centeredAmplitude (A R f m : ℕ) : ℤ :=
  ∑ j ∈ range R,
    extendCoefficients (parityCoefficients (K := ℤ) A R) j *
      2 ^ (R - 1 - j) *
        (if f ≤ j then (m.choose (j - f) : ℤ) else 0)

/-- At the centered degree, clearing the exact power `2^(2*A)` identifies
the guarded native amplitude with the integral umbral pairing. -/
theorem two_pow_mul_centeredAmplitude_eq_umbral
    (A R f m : ℕ) (hR : 1 ≤ R)
    (hcenter : f + m = 2 * A + R - 1) :
    (2 : ℤ) ^ (2 * A) * centeredAmplitude A R f m =
      ∑ i ∈ range (f + m + 1),
        parityInterpolantCore A R i * (centeredKernel f m).coeff i := by
  rw [parity_umbral_eq_sum_taylor]
  have hrange :
      (∑ j : Fin R,
        parityCoefficients (K := ℤ) A R j *
          (taylor (1 : ℤ) (centeredKernel f m)).coeff j.val) =
      ∑ j ∈ range R,
        extendCoefficients (parityCoefficients (K := ℤ) A R) j *
          (taylor (1 : ℤ) (centeredKernel f m)).coeff j := by
    simpa only [extendCoefficients_fin] using
      (Fin.sum_univ_eq_sum_range
        (fun j : ℕ =>
          extendCoefficients (parityCoefficients (K := ℤ) A R) j *
            (taylor (1 : ℤ) (centeredKernel f m)).coeff j) R)
  rw [hrange, centeredAmplitude, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < R := Finset.mem_range.mp hj
  have hjR : j ≤ R - 1 := by omega
  rw [taylor_centeredKernel_coeff]
  by_cases hfj : f ≤ j
  · simp only [if_pos hfj]
    have hpow :
        (2 : ℤ) ^ (2 * A) * 2 ^ (R - 1 - j) =
          2 ^ (m - (j - f)) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      (2 : ℤ) ^ (2 * A) *
          (extendCoefficients (parityCoefficients (K := ℤ) A R) j *
            2 ^ (R - 1 - j) * (m.choose (j - f) : ℤ)) =
        extendCoefficients (parityCoefficients (K := ℤ) A R) j *
          ((2 : ℤ) ^ (2 * A) * 2 ^ (R - 1 - j)) *
            (m.choose (j - f) : ℤ) := by ring
      _ = extendCoefficients (parityCoefficients (K := ℤ) A R) j *
          (2 ^ (m - (j - f)) * (m.choose (j - f) : ℤ)) := by
            rw [hpow]
            ring
  · simp only [if_neg hfj, mul_zero]

theorem centeredAmplitude_eq_zero
    (A R f m : ℕ) (hR : 1 ≤ R)
    (hcenter : f + m = 2 * A + R - 1)
    (hodd : Odd ((R - 1) + f)) :
    centeredAmplitude A R f m = 0 := by
  have hscale := two_pow_mul_centeredAmplitude_eq_umbral A R f m hR hcenter
  rw [centered_umbral_sum_eq_zero A R f m hR hcenter hodd] at hscale
  exact (mul_eq_zero.mp hscale).resolve_left (pow_ne_zero _ (by norm_num))

end
end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
