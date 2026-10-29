import OAI.Algorithms.SubexponentialSAT.SqrtLog.CenteredNativeVanishing

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset Polynomial
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport
noncomputable section

variable {r Q Δ : ℕ}

/-- For `A = 0`, the parity interpolant is the actual parity function over
every coefficient index reached by a kernel of degree `< R`; evaluation at
`-1` then kills every kernel with a positive `(X + 1)` exponent. -/
theorem A_zero_umbral_sum_eq_zero
    (R f m : ℕ) (hdeg : f + m < R) (hm : 1 ≤ m) :
    ∑ i ∈ range (f + m + 1),
      parityInterpolantCore 0 R i * (centeredKernel f m).coeff i = 0 := by
  calc
    (∑ i ∈ range (f + m + 1),
      parityInterpolantCore 0 R i * (centeredKernel f m).coeff i) =
        ∑ i ∈ range (f + m + 1),
          (-1 : ℤ) ^ i * (centeredKernel f m).coeff i := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiR : i < R := by
              have hii : i < f + m + 1 := Finset.mem_range.mp hi
              omega
            let d : Fin R := ⟨i, hiR⟩
            have hp : parityInterpolantCore 0 R i = (-1 : ℤ) ^ i := by
              simpa [d] using parityInterpolantCore_node 0 R d
            rw [hp]
    _ = (centeredKernel f m).eval (-1 : ℤ) := by
      rw [(centeredKernel f m).eval_eq_sum_range'
        (n := f + m + 1)
        (Nat.lt_succ_of_le (natDegree_centeredKernel_le f m))]
      simp only [mul_comm]
    _ = 0 := by
      have hm0 : m ≠ 0 := by omega
      simp [centeredKernel, hm0]

/-- Below the interpolation cutoff, the native guarded amplitude is a
nonnegative power of two times its integral umbral pairing. -/
theorem A_zero_amplitude_eq_scaled_umbral
    (R f m : ℕ) (hdeg : f + m < R) :
    centeredAmplitude 0 R f m =
      (2 : ℤ) ^ (R - 1 - (f + m)) *
        ∑ i ∈ range (f + m + 1),
          parityInterpolantCore 0 R i * (centeredKernel f m).coeff i := by
  rw [parity_umbral_eq_sum_taylor]
  have hrange :
      (∑ j : Fin R,
        parityCoefficients (K := ℤ) 0 R j *
          (taylor (1 : ℤ) (centeredKernel f m)).coeff j.val) =
      ∑ j ∈ range R,
        extendCoefficients (parityCoefficients (K := ℤ) 0 R) j *
          (taylor (1 : ℤ) (centeredKernel f m)).coeff j := by
    simpa only [extendCoefficients_fin] using
      (Fin.sum_univ_eq_sum_range
        (fun j : ℕ =>
          extendCoefficients (parityCoefficients (K := ℤ) 0 R) j *
            (taylor (1 : ℤ) (centeredKernel f m)).coeff j) R)
  rw [hrange, centeredAmplitude, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjR : j < R := Finset.mem_range.mp hj
  rw [taylor_centeredKernel_coeff]
  by_cases hfj : f ≤ j
  · simp only [if_pos hfj]
    by_cases hjN : j ≤ f + m
    · have hpow :
          (2 : ℤ) ^ (R - 1 - j) =
            2 ^ (R - 1 - (f + m)) * 2 ^ (m - (j - f)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hpow]
      ring
    · have hchoose : m.choose (j - f) = 0 :=
        Nat.choose_eq_zero_of_lt (by omega)
      simp [hchoose]
  · simp only [if_neg hfj, mul_zero]

theorem A_zero_centeredAmplitude_eq_zero
    (R f m : ℕ) (hdeg : f + m < R) (hm : 1 ≤ m) :
    centeredAmplitude 0 R f m = 0 := by
  rw [A_zero_amplitude_eq_scaled_umbral R f m hdeg,
    A_zero_umbral_sum_eq_zero R f m hdeg hm, mul_zero]

theorem mismatches_card_lt_activeSet_of_inOrbit_ne
    (i : Fin Δ) (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y) (hne : y ≠ u) :
    (mismatches i u y).card < (activeSet i u).card := by
  obtain ⟨s, rfl⟩ := horbit
  rw [mismatches_swapPositions]
  apply Finset.card_lt_card
  apply Finset.ssubset_iff.mpr
  have hinter : (s ∩ activeSet i u).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hne
    have hswap :
        swapPositions i s u = swapPositions i ∅ u :=
      (swapPositions_eq_iff_inter_activeSet i s ∅ u).2 (by
        simpa [hempty])
    simpa using hswap
  obtain ⟨x, hx⟩ := hinter
  have hxs : x ∈ s := (Finset.mem_inter.mp hx).1
  have hxD : x ∈ activeSet i u := (Finset.mem_inter.mp hx).2
  refine ⟨x, ?_, ?_⟩
  · intro hxsdiff
    exact (Finset.mem_sdiff.mp hxsdiff).2 hxs
  · rw [Finset.insert_subset_iff]
    exact ⟨hxD, Finset.sdiff_subset⟩

/-- Exact source-workbench `A = 0` theorem, now transported to the pinned
native integer entry without admitted steps. -/
theorem entry_eq_zero_of_A_zero_compiled
    (i : Fin Δ) (t : Fin Q) (R : ℕ)
    (hR : 1 ≤ R) (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y) (hne : y ≠ u)
    (hsmall : (activeSet i u).card ≤ R)
    (ht : t ∈ mismatches i u y) :
    entry i t 0 R u y = 0 := by
  have hMD : mismatches i u y ⊆ activeSet i u :=
    mismatches_subset_activeSet_of_inOrbit i u y horbit
  have hMpos : 1 ≤ (mismatches i u y).card :=
    Finset.one_le_card.mpr ⟨t, ht⟩
  have hMle : (mismatches i u y).card ≤ (activeSet i u).card :=
    Finset.card_le_card hMD
  have hMltD : (mismatches i u y).card < (activeSet i u).card :=
    mismatches_card_lt_activeSet_of_inOrbit_ne i u y horbit hne
  have hdegree :
      ((mismatches i u y).card - 1) +
          ((activeSet i u).card - (mismatches i u y).card) < R := by
    omega
  have hm :
      1 ≤ (activeSet i u).card - (mismatches i u y).card := by
    omega
  rw [entry_closed_form_guarded i t 0 R u y horbit ht]
  simp only [Nat.cast_ite, Nat.cast_zero]
  change (-1 : ℤ) ^ ((mismatches i u y).erase t).card *
      centeredAmplitude 0 R
        ((mismatches i u y).card - 1)
        ((activeSet i u).card - (mismatches i u y).card) = 0
  rw [A_zero_centeredAmplitude_eq_zero R
    ((mismatches i u y).card - 1)
    ((activeSet i u).card - (mismatches i u y).card)
    hdegree hm, mul_zero]

end
end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
