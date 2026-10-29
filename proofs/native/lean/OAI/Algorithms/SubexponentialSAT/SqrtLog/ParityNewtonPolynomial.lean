import OAI.Algorithms.SubexponentialSAT.SqrtLog.ParityNewtonValue

/-!
# Newton polynomial for the parity interpolant

The value formula is lifted to an ordinary rational polynomial and identified
with the pinned parity interpolant by degree and its `R` consecutive values.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset Polynomial

noncomputable section

/-- The shifted binomial polynomial `choose (X-A) k`. -/
def shiftedBinomialPolynomialQ (A k : ℕ) : ℚ[X] :=
  ((k.factorial : ℚ)⁻¹ • descPochhammer ℚ k).comp
    (X - C (A : ℚ))

/-- Truncated forward-difference interpolation polynomial for parity. -/
def newtonParityPolynomialQ (A R : ℕ) : ℚ[X] :=
  (-1 : ℚ) ^ A •
    ∑ k ∈ range R, (-2 : ℚ) ^ k • shiftedBinomialPolynomialQ A k

theorem eval_shiftedBinomialPolynomialQ_node (A d k : ℕ) :
    eval (((A + d : ℕ) : ℚ)) (shiftedBinomialPolynomialQ A k) =
      (d.choose k : ℚ) := by
  rw [shiftedBinomialPolynomialQ, eval_comp]
  have harg : (((A + d : ℕ) : ℚ)) - (A : ℚ) = (d : ℚ) := by norm_num
  rw [eval_sub, eval_X, eval_C, harg]
  exact eval_binomialPolynomial_nat k d

theorem eval_newtonParityPolynomialQ_node (A R : ℕ) (d : Fin R) :
    eval ((A + d.val : ℕ) : ℚ) (newtonParityPolynomialQ A R) =
      (-1 : ℚ) ^ (A + d.val) := by
  rw [newtonParityPolynomialQ, eval_smul, eval_finsetSum]
  simp_rw [eval_smul, eval_shiftedBinomialPolynomialQ_node]
  simp only [smul_eq_mul]
  have hsub : range (d.val + 1) ⊆ range R := by
    intro k hk
    simp only [mem_range] at hk ⊢
    omega
  have htruncate :
      (∑ k ∈ range R, (-2 : ℚ) ^ k * (d.val.choose k : ℚ)) =
        ∑ k ∈ range (d.val + 1),
          (-2 : ℚ) ^ k * (d.val.choose k : ℚ) := by
    symm
    apply Finset.sum_subset hsub
    intro k hkR hkSmall
    have hdk : d.val < k := by
      simp only [mem_range, not_lt] at hkSmall
      omega
    rw [Nat.choose_eq_zero_of_lt hdk, Nat.cast_zero, mul_zero]
  rw [htruncate]
  have hbinomial := add_pow (-2 : ℚ) 1 d.val
  simp only [one_pow, mul_one] at hbinomial
  have hsum :
      (∑ k ∈ range (d.val + 1),
          (-2 : ℚ) ^ k * (d.val.choose k : ℚ)) =
        (-1 : ℚ) ^ d.val := by
    rw [← hbinomial]
    norm_num
  rw [hsum, pow_add]

theorem natDegree_shiftedBinomialPolynomialQ_le (A k : ℕ) :
    (shiftedBinomialPolynomialQ A k).natDegree ≤ k := by
  rw [shiftedBinomialPolynomialQ]
  refine (natDegree_comp_le).trans ?_
  have hbase :
      (((k.factorial : ℚ)⁻¹ • descPochhammer ℚ k).natDegree) ≤ k := by
    exact (natDegree_smul_le _ _).trans (by rw [descPochhammer_natDegree])
  have hlin : (X - C (A : ℚ)).natDegree ≤ 1 := by
    exact le_trans (natDegree_sub_le _ _) (by simp [natDegree_C])
  simpa using Nat.mul_le_mul hbase hlin

theorem natDegree_newtonParityPolynomialQ_lt (A R : ℕ) (hR : 1 ≤ R) :
    (newtonParityPolynomialQ A R).natDegree < R := by
  rw [newtonParityPolynomialQ]
  refine lt_of_le_of_lt (natDegree_smul_le _ _) ?_
  refine lt_of_le_of_lt
    (natDegree_sum_le_of_forall_le (range R) _ ?_)
    (Nat.pred_lt (Nat.ne_zero_of_lt hR))
  intro k hk
  have hkR : k ≤ R - 1 := by
    have := mem_range.mp hk
    omega
  exact (natDegree_smul_le _ _).trans
    ((natDegree_shiftedBinomialPolynomialQ_le A k).trans hkR)

/-- The pinned parity polynomial is exactly the truncated Newton interpolant. -/
theorem parityPolynomialQ_eq_newton (A R : ℕ) (hR : 1 ≤ R) :
    parityPolynomialQ A R = newtonParityPolynomialQ A R := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
      (parityPolynomialQ A R) (newtonParityPolynomialQ A R)
      (f := fun d : Fin R => (A + d.val : ℚ))
  · intro d e h
    apply Fin.ext
    have hval : (d.val : ℚ) = (e.val : ℚ) := by linarith
    exact_mod_cast hval
  · intro d
    have hnode : (A : ℚ) + (d.val : ℚ) = ((A + d.val : ℕ) : ℚ) := by
      norm_num
    rw [hnode]
    rw [eval_parityPolynomialQ_nat, eval_newtonParityPolynomialQ_node]
    exact_mod_cast parityInterpolantCore_node A R d
  · simp only [Fintype.card_fin]
    exact max_lt (natDegree_parityPolynomialQ_lt A R hR)
      (natDegree_newtonParityPolynomialQ_lt A R hR)

end

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
