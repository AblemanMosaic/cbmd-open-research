import OAI.Algorithms.SubexponentialSAT.SqrtLog.CenteredKernelReflection

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset Polynomial
noncomputable section

/-- A finite sum cancels when reflection multiplies its two factors by signs
whose product is `-1`.  This isolates the involutive part of centered
vanishing from the parity-specific and kernel-specific calculations. -/
theorem sum_mul_eq_zero_of_reflect
    (N : ℕ) (a b : ℕ → ℤ) (s t : ℤ)
    (ha : ∀ i, i ≤ N → a (N - i) = s * a i)
    (hb : ∀ i, i ≤ N → b (N - i) = t * b i)
    (hst : s * t = -1) :
    ∑ i ∈ range (N + 1), a i * b i = 0 := by
  let S : ℤ := ∑ i ∈ range (N + 1), a i * b i
  have hreflect :
      S = ∑ i ∈ range (N + 1), a (N - i) * b (N - i) := by
    dsimp only [S]
    simpa using
      (sum_range_reflect (fun i => a i * b i) (N + 1)).symm
  have hneg : S = -S := by
    apply hreflect.trans
    calc
      (∑ i ∈ range (N + 1), a (N - i) * b (N - i)) =
          ∑ i ∈ range (N + 1), -(a i * b i) := by
            apply sum_congr rfl
            intro i hi
            have hiN : i ≤ N := by
              simpa using (mem_range.mp hi)
            rw [ha i hiN, hb i hiN]
            calc
              (s * a i) * (t * b i) = (s * t) * (a i * b i) := by ring
              _ = -(a i * b i) := by rw [hst]; ring
      _ = -S := by simp [S]
  linarith

/-- The parity interpolant and centered kernel cancel when their common
reflection axis agrees and the combined reflection exponent is odd. -/
theorem centered_umbral_sum_eq_zero
    (A R f m : ℕ) (hR : 1 ≤ R)
    (hcenter : f + m = 2 * A + R - 1)
    (hodd : Odd ((R - 1) + f)) :
    ∑ i ∈ range (f + m + 1),
      parityInterpolantCore A R i * (centeredKernel f m).coeff i = 0 := by
  have hsign :
      (-1 : ℤ) ^ (R - 1) * (-1 : ℤ) ^ f = -1 := by
    rw [← pow_add, hodd.neg_one_pow]
  apply sum_mul_eq_zero_of_reflect
      (N := f + m)
      (a := parityInterpolantCore A R)
      (b := fun i => (centeredKernel f m).coeff i)
      (s := (-1 : ℤ) ^ (R - 1))
      (t := (-1 : ℤ) ^ f)
  · intro i hi
    have hi' : i ≤ 2 * A + R - 1 := by omega
    simpa [hcenter] using parityInterpolantCore_reflect A R i hi' hR
  · intro i hi
    exact centeredKernel_coeff_reflect f m i hi
  · exact hsign

end
end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
