import OAI.Algorithms.SubexponentialSAT.SqrtLog.EulerBinomialTransform
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ParityCoefficientClosedForm

/-!
# Native scalar amplitude bridge

This module applies the finite Euler transform to the source-bound native
parity coefficients.  It proves no cost claim.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- A triangular finite sum is invariant under exchanging its coordinates. -/
theorem sum_triangle_comm {M : Type*} [AddCommMonoid M]
    (d : ℕ) (F : ℕ → ℕ → M) :
    (∑ s ∈ range (d + 1), ∑ n ∈ range (d - s + 1), F s n) =
      ∑ n ∈ range (d + 1), ∑ s ∈ range (d - n + 1), F s n := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun x => ⟨x.2, x.1⟩)
    ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) <;>
  simp only [Sigma.forall, Finset.mem_sigma, Finset.mem_range] <;>
  omega

/-- The partial alternating binomial sum, including the `m = 0` generalized
coefficient convention required by the native formula. -/
theorem alternating_choose_partial (m D : ℕ) :
    (∑ s ∈ range (D + 1), ((-1 : ℤ) ^ s * (m.choose s : ℤ))) =
      (-1 : ℤ) ^ D * Ring.choose ((m : ℤ) - 1) D := by
  cases m with
  | zero =>
      have hchoose := Ring.choose_neg' (R := ℤ) (1 : ℤ) D
      change Ring.choose (-1 : ℤ) D =
        (((D : ℤ).negOnePow : ℤ) * Ring.multichoose (1 : ℤ) D) at hchoose
      rw [Int.coe_negOnePow_natCast, Ring.multichoose_one] at hchoose
      rw [show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num, hchoose]
      have hsum :
          (∑ s ∈ range (D + 1),
            ((-1 : ℤ) ^ s * ((0 : ℕ).choose s : ℤ))) = 1 := by
        calc
          (∑ s ∈ range (D + 1),
              ((-1 : ℤ) ^ s * ((0 : ℕ).choose s : ℤ))) =
              (-1 : ℤ) ^ 0 * ((0 : ℕ).choose 0 : ℤ) := by
                apply Finset.sum_eq_single 0
                · intro s hs hs0
                  have hspos : 0 < s := Nat.pos_of_ne_zero hs0
                  rw [Nat.choose_eq_zero_of_lt hspos]
                  simp
                · simp
          _ = 1 := by norm_num
      rw [hsum]
      simp [← mul_pow]
  | succ m =>
      simpa [Ring.choose_natCast] using
        (Int.alternating_sum_range_choose_eq_choose (n := m) (m := D))

/-- Natural-index form of the closed parity coefficient, with the triangular
support reindexed by the distance above the diagonal. -/
theorem extendParityCoefficient_closed_form
    (A R j : ℕ) (hj : j < R) :
    extendCoefficients (parityCoefficients (K := ℤ) A R) j =
      ∑ n ∈ range (R - j),
        Ring.choose (-(A : ℤ)) n *
          ((-1 : ℤ) ^ A * (-2 : ℤ) ^ (j + n)) := by
  have hfin := parityCoefficient_closed_form A R ⟨j, hj⟩
  rw [extendCoefficients]
  simp only [hj, ↓reduceDIte]
  rw [hfin]
  have hrange :
      (∑ k : Fin R,
        if j ≤ k.val then
          Ring.choose (-(A : ℤ)) (k.val - j) *
            ((-1 : ℤ) ^ A * (-2 : ℤ) ^ k.val)
        else 0) =
      ∑ k ∈ range R,
        if j ≤ k then
          Ring.choose (-(A : ℤ)) (k - j) *
            ((-1 : ℤ) ^ A * (-2 : ℤ) ^ k)
        else 0 := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun k : ℕ =>
          if j ≤ k then
            Ring.choose (-(A : ℤ)) (k - j) *
              ((-1 : ℤ) ^ A * (-2 : ℤ) ^ k)
          else 0) R)
  rw [hrange]
  have hfilter :
      (range R).filter (fun k => j ≤ k) = Ico j R := by
    ext k
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  calc
    (∑ k ∈ range R,
        if j ≤ k then
          Ring.choose (-(A : ℤ)) (k - j) *
            ((-1 : ℤ) ^ A * (-2 : ℤ) ^ k)
        else 0) =
      ∑ k ∈ (range R).filter (fun k => j ≤ k),
        Ring.choose (-(A : ℤ)) (k - j) *
          ((-1 : ℤ) ^ A * (-2 : ℤ) ^ k) := by
            rw [Finset.sum_filter]
    _ = ∑ k ∈ Ico j R,
        Ring.choose (-(A : ℤ)) (k - j) *
          ((-1 : ℤ) ^ A * (-2 : ℤ) ^ k) := by rw [hfilter]
    _ = ∑ n ∈ range (R - j),
        Ring.choose (-(A : ℤ)) n *
          ((-1 : ℤ) ^ A * (-2 : ℤ) ^ (j + n)) := by
            rw [Finset.sum_Ico_eq_sum_range]
            apply Finset.sum_congr rfl
            intro n hn
            simp

/-- Termwise sign and power-of-two normalization used when inserting the
closed parity coefficient into `centeredAmplitude`. -/
theorem centeredAmplitude_term_normalization
    (A R f s n : ℕ) (hfs : f + s < R) :
    Ring.choose (-(A : ℤ)) n *
          ((-1 : ℤ) ^ A * (-2 : ℤ) ^ (f + s + n)) *
        2 ^ (R - 1 - (f + s)) =
      (-1 : ℤ) ^ (A + f) * 2 ^ (R - 1) *
        (((2 : ℤ) ^ n * negativeBinomialCoeff A n) * (-1 : ℤ) ^ s) := by
  have hchoose := Ring.choose_neg' (R := ℤ) (A : ℤ) n
  change Ring.choose (-(A : ℤ)) n =
    (((n : ℤ).negOnePow : ℤ) * Ring.multichoose (A : ℤ) n) at hchoose
  rw [Int.coe_negOnePow_natCast,
    ← negativeBinomialCoeff_eq_multichoose] at hchoose
  have hpows :
      (2 : ℤ) ^ (f + s + n) * 2 ^ (R - 1 - (f + s)) =
        2 ^ (R - 1) * 2 ^ n := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hsigns :
      (-1 : ℤ) ^ n * (-1 : ℤ) ^ (f + s + n) =
        (-1 : ℤ) ^ f * (-1 : ℤ) ^ s := by
    rw [show f + s + n = (f + s) + n by omega, pow_add, pow_add]
    calc
      (-1 : ℤ) ^ n * (((-1 : ℤ) ^ f * (-1 : ℤ) ^ s) * (-1 : ℤ) ^ n) =
          (((-1 : ℤ) ^ n * (-1 : ℤ) ^ n) *
            ((-1 : ℤ) ^ f * (-1 : ℤ) ^ s)) := by ring
      _ = (-1 : ℤ) ^ f * (-1 : ℤ) ^ s := by
            rw [← mul_pow]
            norm_num
  have hnegpow :
      (-2 : ℤ) ^ (f + s + n) =
        (-1 : ℤ) ^ (f + s + n) * 2 ^ (f + s + n) := by
    rw [← mul_pow]
    norm_num
  rw [hchoose, hnegpow]
  calc
    ((-1 : ℤ) ^ n * negativeBinomialCoeff A n) *
          ((-1 : ℤ) ^ A *
            ((-1 : ℤ) ^ (f + s + n) * 2 ^ (f + s + n))) *
        2 ^ (R - 1 - (f + s)) =
      ((-1 : ℤ) ^ n * (-1 : ℤ) ^ (f + s + n)) *
        ((-1 : ℤ) ^ A * negativeBinomialCoeff A n) *
          (2 ^ (f + s + n) * 2 ^ (R - 1 - (f + s))) := by ring
    _ = ((-1 : ℤ) ^ f * (-1 : ℤ) ^ s) *
        ((-1 : ℤ) ^ A * negativeBinomialCoeff A n) *
          (2 ^ (R - 1) * 2 ^ n) := by rw [hsigns, hpows]
    _ = (-1 : ℤ) ^ (A + f) * 2 ^ (R - 1) *
        (((2 : ℤ) ^ n * negativeBinomialCoeff A n) * (-1 : ℤ) ^ s) := by
          rw [pow_add]
          ring

/-- Inserting the closed native coefficients turns the guarded amplitude into
the finite Euler-transform sum. -/
theorem centeredAmplitude_eq_euler_sum
    (A R f m : ℕ) (hf : f < R) :
    centeredAmplitude A R f m =
      (-1 : ℤ) ^ (A + f) * 2 ^ (R - 1) *
        ∑ n ∈ range (R - 1 - f + 1),
          ((2 : ℤ) ^ n * negativeBinomialCoeff A n) *
            ((-1 : ℤ) ^ (R - 1 - f - n) *
              Ring.choose ((m : ℤ) - 1) (R - 1 - f - n)) := by
  let d := R - 1 - f
  have hRf : R - f = d + 1 := by
    dsimp [d]
    omega
  have hfilter :
      (range R).filter (fun j => f ≤ j) = Ico f R := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  calc
    centeredAmplitude A R f m =
      ∑ j ∈ Ico f R,
        extendCoefficients (parityCoefficients (K := ℤ) A R) j *
          2 ^ (R - 1 - j) * (m.choose (j - f) : ℤ) := by
            rw [centeredAmplitude, ← hfilter, Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hfj : f ≤ j <;> simp [hfj]
    _ = ∑ s ∈ range (d + 1),
        ∑ n ∈ range (d - s + 1),
          (Ring.choose (-(A : ℤ)) n *
              ((-1 : ℤ) ^ A * (-2 : ℤ) ^ (f + s + n))) *
            2 ^ (d - s) * (m.choose s : ℤ) := by
              rw [Finset.sum_Ico_eq_sum_range, hRf]
              apply Finset.sum_congr rfl
              intro s hs
              have hsd : s ≤ d :=
                Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
              have hfs : f + s < R := by
                dsimp [d] at hsd
                omega
              rw [extendParityCoefficient_closed_form A R (f + s) hfs]
              have hrange : R - (f + s) = d - s + 1 := by
                dsimp [d]
                omega
              have hpow : R - 1 - (f + s) = d - s := by
                dsimp [d]
                omega
              rw [hrange, hpow, Nat.add_sub_cancel_left,
                Finset.sum_mul, Finset.sum_mul]
    _ = ∑ s ∈ range (d + 1),
        ∑ n ∈ range (d - s + 1),
          ((-1 : ℤ) ^ (A + f) * 2 ^ (R - 1)) *
            (((2 : ℤ) ^ n * negativeBinomialCoeff A n) *
              ((-1 : ℤ) ^ s * (m.choose s : ℤ))) := by
              apply Finset.sum_congr rfl
              intro s hs
              have hsd : s ≤ d :=
                Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)
              apply Finset.sum_congr rfl
              intro n hn
              have hfs : f + s < R := by
                dsimp [d] at hsd
                omega
              have hpow : R - 1 - (f + s) = d - s := by
                dsimp [d]
                omega
              rw [← hpow]
              rw [centeredAmplitude_term_normalization A R f s n hfs]
              ring
    _ = (-1 : ℤ) ^ (A + f) * 2 ^ (R - 1) *
        (∑ s ∈ range (d + 1),
          ∑ n ∈ range (d - s + 1),
            ((2 : ℤ) ^ n * negativeBinomialCoeff A n) *
              ((-1 : ℤ) ^ s * (m.choose s : ℤ))) := by
              simp_rw [← Finset.mul_sum]
    _ = (-1 : ℤ) ^ (A + f) * 2 ^ (R - 1) *
        (∑ n ∈ range (d + 1),
          ∑ s ∈ range (d - n + 1),
            ((2 : ℤ) ^ n * negativeBinomialCoeff A n) *
              ((-1 : ℤ) ^ s * (m.choose s : ℤ))) := by
              rw [sum_triangle_comm]
    _ = (-1 : ℤ) ^ (A + f) * 2 ^ (R - 1) *
        ∑ n ∈ range (d + 1),
          ((2 : ℤ) ^ n * negativeBinomialCoeff A n) *
            ((-1 : ℤ) ^ (d - n) *
              Ring.choose ((m : ℤ) - 1) (d - n)) := by
              congr 1
              apply Finset.sum_congr rfl
              intro n hn
              rw [← Finset.mul_sum, alternating_choose_partial]
    _ = (-1 : ℤ) ^ (A + f) * 2 ^ (R - 1) *
        ∑ n ∈ range (R - 1 - f + 1),
          ((2 : ℤ) ^ n * negativeBinomialCoeff A n) *
            ((-1 : ℤ) ^ (R - 1 - f - n) *
              Ring.choose ((m : ℤ) - 1) (R - 1 - f - n)) := by rfl

/-- `masterAlpha` in the same orientation as the Euler-transform output. -/
theorem masterAlpha_eq_euler_sum
    (A R f m : ℕ) (hf : f < R) :
    masterAlpha A R (f + m + 1) f =
      (-1 : ℤ) ^ A *
        ∑ q ∈ range (R - 1 - f + 1),
          negativeBinomialCoeff A q *
            Ring.choose ((A : ℤ) + (R - 1 - f) - m)
              (R - 1 - f - q) := by
  let d := R - 1 - f
  have hupper :
      (A : ℤ) + (R : ℤ) - ((f + m + 1 : ℕ) : ℤ) =
        (A : ℤ) + (d : ℤ) - (m : ℤ) := by
    dsimp [d]
    rw [Nat.cast_sub (by omega : f ≤ R - 1)]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (by omega : R ≠ 0))]
    push_cast
    ring
  rw [masterAlpha]
  rw [hupper]
  rw [← Finset.sum_range_reflect]
  dsimp [d]
  apply congrArg ((-1 : ℤ) ^ A * ·)
  apply Finset.sum_congr rfl
  intro q hq
  have hqd : q ≤ R - 1 - f :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have hcast :
      ((R - 1 - f : ℕ) : ℤ) = (R : ℤ) - 1 - (f : ℤ) := by
    rw [Nat.cast_sub (by omega : f ≤ R - 1)]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (by omega : R ≠ 0))]
    norm_num
  have hrev :
      R - 1 - f - (R - 1 - f - q) = q := by omega
  simp only [generalizedChoose_eq_ringChoose]
  rw [hrev, hcast]
  ring

/-- The pure scalar bridge required by the native entry theorem.  The only
geometric input still needed by callers is the exact relation
`δ = f + m + 1`. -/
theorem signed_centeredAmplitude_eq_masterNumerator
    (A R f m : ℕ) (hf : f < R) :
    (-1 : ℤ) ^ f * centeredAmplitude A R f m =
      masterNumerator A R (f + m + 1) f := by
  rw [centeredAmplitude_eq_euler_sum A R f m hf]
  rw [masterNumerator, masterAlpha_eq_euler_sum A R f m hf]
  rw [finite_euler_binomial_transform A m (R - 1 - f)]
  have hsign :
      (-1 : ℤ) ^ f * (-1 : ℤ) ^ (A + f) = (-1 : ℤ) ^ A := by
    rw [pow_add]
    calc
      (-1 : ℤ) ^ f * ((-1 : ℤ) ^ A * (-1 : ℤ) ^ f) =
          ((-1 : ℤ) ^ f * (-1 : ℤ) ^ f) * (-1 : ℤ) ^ A := by ring
      _ = (-1 : ℤ) ^ A := by
            rw [← mul_pow]
            norm_num
  have hcast :
      ((R - 1 - f : ℕ) : ℤ) = (R : ℤ) - 1 - (f : ℤ) := by
    rw [Nat.cast_sub (by omega : f ≤ R - 1)]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (by omega : R ≠ 0))]
    norm_num
  rw [hcast]
  calc
    (-1 : ℤ) ^ f *
        ((-1 : ℤ) ^ (A + f) * 2 ^ (R - 1) *
          ∑ q ∈ range (R - 1 - f + 1),
            negativeBinomialCoeff A q *
              Ring.choose ((A : ℤ) + ((R : ℤ) - 1 - f) - m)
                (R - 1 - f - q)) =
      ((-1 : ℤ) ^ f * (-1 : ℤ) ^ (A + f)) *
        (2 ^ (R - 1) *
          ∑ q ∈ range (R - 1 - f + 1),
            negativeBinomialCoeff A q *
              Ring.choose ((A : ℤ) + ((R : ℤ) - 1 - f) - m)
                (R - 1 - f - q)) := by ring
    _ = (-1 : ℤ) ^ A *
        (2 ^ (R - 1) *
          ∑ q ∈ range (R - 1 - f + 1),
            negativeBinomialCoeff A q *
              Ring.choose ((A : ℤ) + ((R : ℤ) - 1 - f) - m)
                (R - 1 - f - q)) := by rw [hsign]
    _ = 2 ^ (R - 1) *
        ((-1 : ℤ) ^ A *
          ∑ q ∈ range (R - 1 - f + 1),
            negativeBinomialCoeff A q *
              Ring.choose ((A : ℤ) + ((R : ℤ) - 1 - f) - m)
                (R - 1 - f - q)) := by ring

/-- Source-facing master formula for every in-orbit entry whose mismatch count
lies in the native support range.  This closes the former scalar-bridge
hypothesis without changing `entry`, `masterNumerator`, or their signs. -/
theorem entry_eq_masterNumerator
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y)
    (hMleR : (mismatches i u y).card ≤ R) :
    entry i t A R u y =
      masterNumerator A R (activeSet i u).card
        ((mismatches i u y).card - 1) := by
  apply entry_eq_masterNumerator_of_scalar_bridge
    i t A R u y horbit ht
  have hMD : mismatches i u y ⊆ activeSet i u :=
    mismatches_subset_activeSet_of_inOrbit i u y horbit
  have hMpos : 1 ≤ (mismatches i u y).card :=
    Finset.one_le_card.mpr ⟨t, ht⟩
  have hMle : (mismatches i u y).card ≤ (activeSet i u).card :=
    Finset.card_le_card hMD
  have hdelta :
      (activeSet i u).card =
        ((mismatches i u y).card - 1) +
          ((activeSet i u).card - (mismatches i u y).card) + 1 := by
    omega
  have hscalar := signed_centeredAmplitude_eq_masterNumerator A R
      ((mismatches i u y).card - 1)
      ((activeSet i u).card - (mismatches i u y).card)
      (by omega)
  rw [← hdelta] at hscalar
  exact hscalar

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
