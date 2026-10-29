import OAI.Algorithms.SubexponentialSAT.SqrtLog.MasterAmplitudeBinomialBridge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ParityClosedForm

/-!
# Finite Euler transform for the native amplitude

This module isolates the finite binomial transform between the proved native
parity-coefficient formula and the executable `masterAlpha` sum.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset

/-- Splitting a multiset by a marked submultiset gives the finite coefficient
identity behind the substitution `x ↦ x / (1 - x)`. -/
theorem two_pow_mul_negativeBinomialCoeff (A n : ℕ) :
    (2 : ℤ) ^ n * negativeBinomialCoeff A n =
      ∑ q ∈ range (n + 1),
        negativeBinomialCoeff A q *
          negativeBinomialCoeff (A + q) (n - q) := by
  by_cases hA : A = 0
  · subst A
    cases n with
    | zero => simp [negativeBinomialCoeff]
    | succ n =>
        simp only [negativeBinomialCoeff, zero_add]
        have hleft : (n + 1 - 1).choose (n + 1) = 0 :=
          Nat.choose_eq_zero_of_lt (by omega)
        rw [hleft]
        simp only [Nat.cast_zero, mul_zero]
        symm
        apply Finset.sum_eq_zero
        intro q hq
        by_cases hq0 : q = 0
        · subst q
          simp
        · have hlt : q - 1 < q := Nat.sub_lt (Nat.zero_lt_of_ne_zero hq0) (by omega)
          rw [Nat.choose_eq_zero_of_lt hlt]
          simp
  · have hApos : 1 ≤ A := (Nat.one_le_iff_ne_zero).2 hA
    have hterm (q : ℕ) (hq : q < n + 1) :
        negativeBinomialCoeff A q *
            negativeBinomialCoeff (A + q) (n - q) =
          (n.choose q : ℤ) * negativeBinomialCoeff A n := by
      have hqn : q ≤ n := Nat.lt_succ_iff.mp hq
      simp only [negativeBinomialCoeff]
      have htop : A + q + (n - q) - 1 = A + n - 1 := by omega
      rw [htop]
      have hbase : (A + n - 1) - (n - q) = A + q - 1 := by omega
      have hrest : n - (n - q) = q := by omega
      have hchoose :=
        Nat.choose_mul (n := A + n - 1) (k := n) (s := n - q)
          (Nat.sub_le n q)
      rw [Nat.choose_symm hqn, hbase, hrest] at hchoose
      exact_mod_cast (by simpa [mul_comm] using hchoose.symm)
    calc
      (2 : ℤ) ^ n * negativeBinomialCoeff A n =
          (∑ q ∈ range (n + 1), (n.choose q : ℤ)) *
            negativeBinomialCoeff A n := by
              congr 1
              norm_num only [← Nat.cast_sum]
              rw [Nat.sum_range_choose]
              norm_num
      _ = ∑ q ∈ range (n + 1),
            (n.choose q : ℤ) * negativeBinomialCoeff A n := by
              rw [Finset.sum_mul]
      _ = ∑ q ∈ range (n + 1),
            negativeBinomialCoeff A q *
              negativeBinomialCoeff (A + q) (n - q) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact (hterm q (Finset.mem_range.mp hq)).symm

/-- A signed multichoose convolution.  This is Chu--Vandermonde after writing
`multichoose a r` as `(-1)^r choose (-a) r`. -/
theorem signed_multichoose_convolution (a b : ℤ) (D : ℕ) :
    (∑ r ∈ range (D + 1),
        Ring.multichoose a r *
          ((-1 : ℤ) ^ (D - r) * Ring.choose b (D - r))) =
      Ring.choose (a + D - b - 1) D := by
  have hterm (r : ℕ) (hr : r < D + 1) :
      Ring.multichoose a r *
          ((-1 : ℤ) ^ (D - r) * Ring.choose b (D - r)) =
        (-1 : ℤ) ^ D *
          (Ring.choose (-a) r * Ring.choose b (D - r)) := by
    have hrD : r ≤ D := Nat.lt_succ_iff.mp hr
    have hchoose := Ring.choose_neg' (R := ℤ) a r
    change Ring.choose (-a) r =
      (((r : ℤ).negOnePow : ℤ) * Ring.multichoose a r) at hchoose
    rw [Int.coe_negOnePow_natCast] at hchoose
    have hmulti : Ring.multichoose a r =
        (-1 : ℤ) ^ r * Ring.choose (-a) r := by
      calc
        Ring.multichoose a r =
            (((-1 : ℤ) ^ r * (-1 : ℤ) ^ r) * Ring.multichoose a r) := by
              simp [← mul_pow]
        _ = (-1 : ℤ) ^ r * Ring.choose (-a) r := by
              rw [hchoose]
              ring
    have hsign : (-1 : ℤ) ^ r * (-1 : ℤ) ^ (D - r) = (-1 : ℤ) ^ D := by
      rw [← pow_add]
      congr 1
      omega
    calc
      Ring.multichoose a r *
          ((-1 : ℤ) ^ (D - r) * Ring.choose b (D - r)) =
        ((-1 : ℤ) ^ r * Ring.choose (-a) r) *
          ((-1 : ℤ) ^ (D - r) * Ring.choose b (D - r)) := by
            rw [hmulti]
      _ = (-1 : ℤ) ^ D *
          (Ring.choose (-a) r * Ring.choose b (D - r)) := by
            rw [← hsign]
            ring
  calc
    (∑ r ∈ range (D + 1),
        Ring.multichoose a r *
          ((-1 : ℤ) ^ (D - r) * Ring.choose b (D - r))) =
      ∑ r ∈ range (D + 1),
        (-1 : ℤ) ^ D *
          (Ring.choose (-a) r * Ring.choose b (D - r)) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hterm r (Finset.mem_range.mp hr)
    _ = (-1 : ℤ) ^ D * Ring.choose (b - a) D := by
          rw [← Finset.mul_sum, choose_int_convolution]
          congr 2
          ring
    _ = Ring.choose (a + D - b - 1) D := by
          have hchoose := Ring.choose_neg' (R := ℤ) (a - b) D
          change Ring.choose (-(a - b)) D =
            (((D : ℤ).negOnePow : ℤ) * Ring.multichoose (a - b) D) at hchoose
          rw [Int.coe_negOnePow_natCast, Ring.multichoose_eq] at hchoose
          have hneg : -(a - b) = b - a := by ring
          rw [hneg] at hchoose
          calc
            (-1 : ℤ) ^ D * Ring.choose (b - a) D =
                (-1 : ℤ) ^ D *
                  ((-1 : ℤ) ^ D * Ring.choose (a - b + D - 1) D) := by
                    rw [hchoose]
            _ = Ring.choose (a - b + D - 1) D := by
                  rw [← mul_assoc, ← pow_add]
                  have heven : (-1 : ℤ) ^ (D + D) = 1 := by
                    rw [show D + D = 2 * D by omega, pow_mul]
                    norm_num
                  rw [heven, one_mul]
            _ = Ring.choose (a + D - b - 1) D := by
                  congr 1
                  ring

/-- The finite Euler transform in the exact integer normalization used by the
native amplitude. -/
theorem finite_euler_binomial_transform (A m d : ℕ) :
    (∑ n ∈ range (d + 1),
        ((2 : ℤ) ^ n * negativeBinomialCoeff A n) *
          ((-1 : ℤ) ^ (d - n) *
            Ring.choose ((m : ℤ) - 1) (d - n))) =
      ∑ q ∈ range (d + 1),
        negativeBinomialCoeff A q *
          Ring.choose ((A : ℤ) + d - m) (d - q) := by
  calc
    (∑ n ∈ range (d + 1),
        ((2 : ℤ) ^ n * negativeBinomialCoeff A n) *
          ((-1 : ℤ) ^ (d - n) *
            Ring.choose ((m : ℤ) - 1) (d - n))) =
      ∑ n ∈ range (d + 1),
        ∑ q ∈ range (n + 1),
          (negativeBinomialCoeff A q *
            negativeBinomialCoeff (A + q) (n - q)) *
              ((-1 : ℤ) ^ (d - n) *
                Ring.choose ((m : ℤ) - 1) (d - n)) := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  rw [two_pow_mul_negativeBinomialCoeff, Finset.sum_mul]
    _ = ∑ q ∈ range (d + 1),
        ∑ n ∈ Ico q (d + 1),
          (negativeBinomialCoeff A q *
            negativeBinomialCoeff (A + q) (n - q)) *
              ((-1 : ℤ) ^ (d - n) *
                Ring.choose ((m : ℤ) - 1) (d - n)) := by
                  simpa [Nat.Ico_zero_eq_range] using
                    (Finset.sum_Ico_Ico_comm 0 (d + 1)
                      (fun q n =>
                        (negativeBinomialCoeff A q *
                          negativeBinomialCoeff (A + q) (n - q)) *
                            ((-1 : ℤ) ^ (d - n) *
                              Ring.choose ((m : ℤ) - 1) (d - n)))).symm
    _ = ∑ q ∈ range (d + 1),
        negativeBinomialCoeff A q *
          (∑ r ∈ range (d - q + 1),
            negativeBinomialCoeff (A + q) r *
              ((-1 : ℤ) ^ (d - q - r) *
                Ring.choose ((m : ℤ) - 1) (d - q - r))) := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  have hqd : q ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
                  rw [Finset.sum_Ico_eq_sum_range]
                  rw [show d + 1 - q = d - q + 1 by omega]
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro r hr
                  have hrdq : r ≤ d - q :=
                    Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
                  have hsub : d - (q + r) = d - q - r := by omega
                  simp only [Nat.add_sub_cancel_left, hsub]
                  ring
    _ = ∑ q ∈ range (d + 1),
        negativeBinomialCoeff A q *
          Ring.choose ((A : ℤ) + d - m) (d - q) := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  have hqd : q ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
                  simp_rw [negativeBinomialCoeff_eq_multichoose]
                  rw [signed_multichoose_convolution]
                  congr 2
                  rw [Nat.cast_add, Nat.cast_sub hqd]
                  ring

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
