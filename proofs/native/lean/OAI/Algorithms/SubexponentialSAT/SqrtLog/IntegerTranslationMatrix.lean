import OAI.Algorithms.SubexponentialSAT.SqrtLog.ParityClosedForm

/-!
# Integer translation matrices

This extends the native upper Pascal translation matrix from natural shifts to
integer shifts.  Chu--Vandermonde then gives the composition law and the exact
inverse needed for coefficient extraction.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset Matrix

def integerTranslation (a : ℤ) (R : ℕ) : Matrix (Fin R) (Fin R) ℤ :=
  fun i j => if i.val ≤ j.val then Ring.choose a (j.val - i.val) else 0

@[simp] theorem integerTranslation_apply (a : ℤ) (R : ℕ) (i j : Fin R) :
    integerTranslation a R i j =
      if i.val ≤ j.val then Ring.choose a (j.val - i.val) else 0 := rfl

theorem integerTranslation_mul (a b : ℤ) (R : ℕ) :
    integerTranslation a R * integerTranslation b R =
      integerTranslation (a + b) R := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i.val ≤ j.val
  · rw [integerTranslation_apply, if_pos hij]
    simp only [integerTranslation]
    rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ =>
        (if i.val ≤ k then Ring.choose a (k - i.val) else 0) *
          (if k ≤ j.val then Ring.choose b (j.val - k) else 0)) R]
    have hfilter :
        (filter (fun k : ℕ => i.val ≤ k ∧ k ≤ j.val) (range R)) =
          Ico i.val (j.val + 1) := by
      ext k
      simp only [mem_filter, mem_range, mem_Ico]
      constructor
      · intro hk
        omega
      · intro hk
        omega
    calc
      (∑ k ∈ range R,
          (if i.val ≤ k then Ring.choose a (k - i.val) else 0) *
            (if k ≤ j.val then Ring.choose b (j.val - k) else 0)) =
          ∑ k ∈ filter (fun k : ℕ => i.val ≤ k ∧ k ≤ j.val) (range R),
            Ring.choose a (k - i.val) * Ring.choose b (j.val - k) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro k hkR
              by_cases hki : i.val ≤ k
              · by_cases hkj : k ≤ j.val
                · simp [hki, hkj]
                · simp [hki, hkj]
              · simp [hki]
      _ = ∑ k ∈ Ico i.val (j.val + 1),
            Ring.choose a (k - i.val) * Ring.choose b (j.val - k) := by
              rw [hfilter]
      _ = ∑ n ∈ range (j.val - i.val + 1),
            Ring.choose a n * Ring.choose b (j.val - i.val - n) := by
              rw [sum_Ico_eq_sum_range]
              have hrange : j.val + 1 - i.val = j.val - i.val + 1 := by
                omega
              rw [hrange]
              apply Finset.sum_congr rfl
              intro n hn
              have hnle : n ≤ j.val - i.val := by
                simpa only [mem_range, Nat.lt_add_one_iff] using hn
              have hleft : i.val + n - i.val = n := by omega
              have hright : j.val - (i.val + n) = j.val - i.val - n := by
                omega
              rw [hleft, hright]
      _ = Ring.choose (a + b) (j.val - i.val) :=
        choose_int_convolution a b (j.val - i.val)
  · rw [integerTranslation_apply, if_neg hij]
    rw [Finset.sum_eq_zero]
    intro k hk
    by_cases hik : i.val ≤ k.val
    · have hkj : ¬k.val ≤ j.val := by omega
      simp [integerTranslation, hik, hkj]
    · simp [integerTranslation, hik]

theorem integerTranslation_neg_mul (a : ℤ) (R : ℕ) :
    integerTranslation (-a) R * integerTranslation a R = 1 := by
  rw [integerTranslation_mul]
  simp only [neg_add_cancel]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [integerTranslation]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hle : i.val ≤ j.val
    · have hpos : 0 < j.val - i.val := by omega
      rw [integerTranslation_apply, if_pos hle]
      rw [Matrix.one_apply, if_neg hij]
      change Ring.choose (0 : ℤ) (j.val - i.val) = 0
      obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
      rw [hn, Ring.choose_zero_succ]
    · simp [integerTranslation, hle, hij]

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
