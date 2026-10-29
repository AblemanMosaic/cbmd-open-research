import OAI.Algorithms.SubexponentialSAT.SqrtLog.EntryClosedFormAssemble
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.Roots

/-!
# Reflection of the parity interpolant

This module replaces the admitted reflection step by identifying the finite
binomial-basis interpolant with an ordinary rational polynomial of degree
strictly less than the interpolation length.  The reflection is then forced
by equality at the same consecutive interpolation nodes.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation
open Polynomial

noncomputable section

/-- The integer-valued parity interpolant, duplicated here so the proof module
does not import the workbench file that still contains other admitted goals. -/
noncomputable def parityInterpolantCore (A R : ℕ) (x : ℕ) : ℤ :=
  ∑ j : Fin R, parityCoefficients (K := ℤ) A R j * (x.choose j.val : ℤ)

/-- The rational polynomial whose value at a natural number is the parity
interpolant.  `descPochhammer j / j!` is the polynomial binomial basis. -/
noncomputable def parityPolynomialQ (A R : ℕ) : ℚ[X] :=
  ∑ j : Fin R,
    parityCoefficients (K := ℚ) A R j •
      ((j.val.factorial : ℚ)⁻¹ • descPochhammer ℚ j.val)

theorem eval_binomialPolynomial_nat (j x : ℕ) :
    eval (x : ℚ) ((j.factorial : ℚ)⁻¹ • descPochhammer ℚ j) =
      (x.choose j : ℚ) := by
  rw [eval_smul]
  simp only [smul_eq_mul]
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [div_eq_mul_inv, mul_comm]

theorem eval_parityPolynomialQ_nat (A R x : ℕ) :
    eval (x : ℚ) (parityPolynomialQ A R) =
      (parityInterpolantCore A R x : ℚ) := by
  rw [parityPolynomialQ, eval_finsetSum, parityInterpolantCore, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [eval_smul]
  change parityCoefficients (K := ℚ) A R j *
      eval (x : ℚ) ((j.val.factorial : ℚ)⁻¹ • descPochhammer ℚ j.val) =
    ((parityCoefficients (K := ℤ) A R j * (x.choose j.val : ℤ) : ℤ) : ℚ)
  rw [eval_binomialPolynomial_nat, Int.cast_mul, parityCoefficients_intCast]
  rfl

theorem parityInterpolantCore_node (A R : ℕ) (d : Fin R) :
    parityInterpolantCore A R (A + d.val) =
      (-1 : ℤ) ^ (A + d.val) := by
  exact parityCoefficients_spec (K := ℤ) A R d

theorem natDegree_parityPolynomialQ_lt (A R : ℕ) (hR : 1 ≤ R) :
    (parityPolynomialQ A R).natDegree < R := by
  rw [parityPolynomialQ]
  refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le Finset.univ _ ?_)
    (Nat.pred_lt (Nat.ne_zero_of_lt hR))
  intro j _
  refine (natDegree_smul_le _ _).trans ((natDegree_smul_le _ _).trans ?_)
  rw [descPochhammer_natDegree]
  exact Nat.le_pred_of_lt j.isLt

/-- Polynomial reflection forced by its values at the `R` interpolation
nodes. -/
theorem parityPolynomialQ_reflect (A R : ℕ) (hR : 1 ≤ R) :
    (parityPolynomialQ A R).comp
        (C ((2 * A + R - 1 : ℕ) : ℚ) - X) =
      (-1 : ℚ) ^ (R - 1) • parityPolynomialQ A R := by
  let p := parityPolynomialQ A R
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
      (p.comp (C ((2 * A + R - 1 : ℕ) : ℚ) - X))
      ((-1 : ℚ) ^ (R - 1) • p)
      (f := fun d : Fin R => (A + d.val : ℚ))
  · intro d e h
    apply Fin.ext
    have hval : (d.val : ℚ) = (e.val : ℚ) := by linarith
    exact_mod_cast hval
  · intro d
    simp only [eval_comp, eval_sub, eval_C, eval_X, eval_smul, smul_eq_mul]
    have hd : d.val ≤ R - 1 := Nat.le_pred_of_lt d.isLt
    have hreflect :
        ((2 * A + R - 1 : ℕ) : ℚ) - (A + d.val : ℚ) =
          (A + (R - 1 - d.val) : ℕ) := by
      have hn : 2 * A + R - 1 - (A + d.val) = A + (R - 1 - d.val) := by
        omega
      have hle : A + d.val ≤ 2 * A + R - 1 := by omega
      calc
        ((2 * A + R - 1 : ℕ) : ℚ) - (A + d.val : ℚ) =
            ((2 * A + R - 1 : ℕ) : ℚ) - ((A + d.val : ℕ) : ℚ) := by norm_num
        _ = ((2 * A + R - 1 - (A + d.val) : ℕ) : ℚ) := by
          rw [Nat.cast_sub hle]
        _ = ((A + (R - 1 - d.val) : ℕ) : ℚ) := by rw [hn]
    dsimp [p]
    rw [hreflect, eval_parityPolynomialQ_nat]
    have hnode : (A + d.val : ℚ) = ((A + d.val : ℕ) : ℚ) := by norm_num
    rw [hnode, eval_parityPolynomialQ_nat]
    let d' : Fin R := ⟨R - 1 - d.val, by omega⟩
    rw [show A + (R - 1 - d.val) = A + d'.val by rfl,
      parityInterpolantCore_node A R d', parityInterpolantCore_node A R d]
    dsimp [d']
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
    have hsum : (R - 1 - d.val) + d.val = R - 1 := Nat.sub_add_cancel hd
    have heven : (-1 : ℚ) ^ (2 * d.val) = 1 := by
      rw [pow_mul]
      norm_num
    calc
      (-1 : ℚ) ^ (A + (R - 1 - d.val)) =
          (-1 : ℚ) ^ (A + (R - 1 - d.val)) * (-1 : ℚ) ^ (2 * d.val) := by
            rw [heven, mul_one]
      _ = (-1 : ℚ) ^ (A + (R - 1 - d.val) + 2 * d.val) := by
            exact (pow_add _ _ _).symm
      _ = (-1 : ℚ) ^ ((R - 1) + (A + d.val)) := by
            congr 1 <;> omega
      _ = (-1 : ℚ) ^ (R - 1) * (-1 : ℚ) ^ (A + d.val) := by rw [pow_add]
  · simp only [Fintype.card_fin]
    apply max_lt
    · refine lt_of_le_of_lt natDegree_comp_le ?_
      have hp := natDegree_parityPolynomialQ_lt A R hR
      have hlin : (C ((2 * A + R - 1 : ℕ) : ℚ) - X).natDegree ≤ 1 := by
        exact le_trans (natDegree_sub_le _ _) (by simp [natDegree_C])
      exact lt_of_le_of_lt (Nat.mul_le_mul_left _ hlin) (by simpa using hp)
    · exact lt_of_le_of_lt (natDegree_smul_le _ _) (natDegree_parityPolynomialQ_lt A R hR)

/-- Integer-valued reflection, now obtained from the polynomial identity. -/
theorem parityInterpolantCore_reflect (A R x : ℕ)
    (hx : x ≤ 2 * A + R - 1) (hR : 1 ≤ R) :
    parityInterpolantCore A R (2 * A + R - 1 - x) =
      (-1 : ℤ) ^ (R - 1) * parityInterpolantCore A R x := by
  have href := congrArg (fun q : ℚ[X] => eval (x : ℚ) q)
    (parityPolynomialQ_reflect A R hR)
  simp only [eval_comp, eval_sub, eval_C, eval_X, eval_smul, smul_eq_mul] at href
  have hcast :
      ((2 * A + R - 1 : ℕ) : ℚ) - (x : ℚ) =
        (2 * A + R - 1 - x : ℕ) := by
    rw [← Nat.cast_sub hx]
  rw [hcast, eval_parityPolynomialQ_nat, eval_parityPolynomialQ_nat] at href
  exact_mod_cast href

end

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
