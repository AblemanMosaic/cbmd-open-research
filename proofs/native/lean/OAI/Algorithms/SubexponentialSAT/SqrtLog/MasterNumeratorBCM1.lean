import OAI.Algorithms.SubexponentialSAT.SqrtLog.MasterNumeratorShared

/-!
# BCM-1 recurrence kernel

This module binds the source-level master numerator to the exact two-recurrence
kernel described by BCM-1.  Both coefficient tables are generated once.  The
outer parity sign is a conditional negation, not a charged multiplication.

The value proof is general.  A separate meter/audit owns the arithmetic-count
claim; allocation, indexing, traversal, and exponent construction are still
outside BCM-1 and no whole-algorithm speedup is asserted here.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- Multiplicative step for the nonnegative negative-binomial factor. -/
theorem negativeBinomialCoeff_mul_step (A k : ℕ) :
    negativeBinomialCoeff A k * ((A + k : ℕ) : ℤ) =
      negativeBinomialCoeff A (k + 1) * ((k + 1 : ℕ) : ℤ) := by
  rw [← negativeBinomialLinear_eq A k,
    ← negativeBinomialLinear_eq A (k + 1),
    negativeBinomialLinear, negativeBinomialLinear,
    generalizedChooseLinear_eq_ringChoose,
    generalizedChooseLinear_eq_ringChoose]
  have h := ringChoose_mul_step (-(A : ℤ)) k
  calc
    (-1 : ℤ) ^ k * Ring.choose (-(A : ℤ)) k * ((A + k : ℕ) : ℤ) =
        (-1 : ℤ) ^ (k + 1) *
          (Ring.choose (-(A : ℤ)) k * (-(A : ℤ) - (k : ℤ))) := by
            push_cast
            ring
    _ = (-1 : ℤ) ^ (k + 1) *
          (Ring.choose (-(A : ℤ)) (k + 1) * ((k + 1 : ℕ) : ℤ)) := by
            rw [h]
    _ = ((-1 : ℤ) ^ (k + 1) * Ring.choose (-(A : ℤ)) (k + 1)) *
          ((k + 1 : ℕ) : ℤ) := by ring

/-- `[g_d,…,g₀]`, built directly by the BCM-1 recurrence
`g_(k+1)=g_k(A+k)/(k+1)`. -/
def negativeBinomialRevBCM1 (A : ℕ) : ℕ → List ℤ
  | 0 => [1]
  | d + 1 =>
      let previous := negativeBinomialRevBCM1 A d
      let next := previous.headD 0 * ((A + d : ℕ) : ℤ) /
        ((d + 1 : ℕ) : ℤ)
      next :: previous

theorem negativeBinomialRevBCM1_eq (A : ℕ) : ∀ d : ℕ,
    negativeBinomialRevBCM1 A d =
      (List.range (d + 1)).reverse.map (negativeBinomialCoeff A) := by
  intro d
  induction d with
  | zero => simp [negativeBinomialRevBCM1, negativeBinomialCoeff]
  | succ d ih =>
      have hstep :
          negativeBinomialCoeff A d * ((A + d : ℕ) : ℤ) /
              ((d + 1 : ℕ) : ℤ) =
            negativeBinomialCoeff A (d + 1) := by
        apply Int.ediv_eq_of_eq_mul_left
        · omega
        · exact negativeBinomialCoeff_mul_step A d
      have hstep' :
          negativeBinomialCoeff A d * ((A : ℤ) + (d : ℤ)) /
              ((d : ℤ) + 1) =
            negativeBinomialCoeff A (d + 1) := by
        simpa using hstep
      rw [negativeBinomialRevBCM1, ih]
      simp [List.range_succ, hstep']

def negativeBinomialTableBCM1 (A d : ℕ) : List ℤ :=
  (negativeBinomialRevBCM1 A d).reverse

theorem negativeBinomialTableBCM1_eq (A d : ℕ) :
    negativeBinomialTableBCM1 A d =
      (List.range (d + 1)).map (negativeBinomialCoeff A) := by
  simp [negativeBinomialTableBCM1, negativeBinomialRevBCM1_eq,
    List.map_reverse]

theorem negativeBinomialTableBCM1_getD (A d k : ℕ) (hk : k ≤ d) :
    (negativeBinomialTableBCM1 A d).getD k 0 = negativeBinomialCoeff A k := by
  rw [negativeBinomialTableBCM1_eq]
  have hk' : k < d + 1 := by omega
  simp [List.getD, hk']

/-- BCM-1 treats the parity sign as an uncharged conditional negation. -/
def applyParitySign (A : ℕ) (x : ℤ) : ℤ :=
  if Even A then x else -x

theorem applyParitySign_eq (A : ℕ) (x : ℤ) :
    applyParitySign A x = (-1 : ℤ) ^ A * x := by
  rcases Nat.even_or_odd A with h | h
  · simp [applyParitySign, h]
  · have hn : ¬ Even A := Nat.not_even_iff_odd.mpr h
    simp [applyParitySign, hn, h.neg_one_pow]

/-- The two shared recurrence tables followed by their finite convolution. -/
def masterAlphaBCM1 (A R δ f : ℕ) : ℤ :=
  let d := R - 1 - f
  let chooseTable := generalizedChooseTable
    ((A : ℤ) + (R : ℤ) - (δ : ℤ)) d
  let negativeTable := negativeBinomialTableBCM1 A d
  let total := ∑ k ∈ range (d + 1),
    chooseTable.getD k 0 * negativeTable.getD (d - k) 0
  applyParitySign A total

def masterNumeratorBCM1 (A R δ f : ℕ) : ℤ :=
  2 ^ (R - 1) * masterAlphaBCM1 A R δ f

theorem masterAlphaBCM1_eq_masterAlpha (A R δ f : ℕ) :
    masterAlphaBCM1 A R δ f = masterAlpha A R δ f := by
  simp only [masterAlphaBCM1, masterAlpha, applyParitySign_eq]
  apply congrArg ((-1 : ℤ) ^ A * ·)
  apply Finset.sum_congr rfl
  intro k hk
  have hkle : k ≤ R - 1 - f := by
    have := Finset.mem_range.mp hk
    omega
  rw [generalizedChooseTable_getD _ _ _ hkle,
    negativeBinomialTableBCM1_getD _ _ _ (Nat.sub_le _ _),
    generalizedChoose_eq_ringChoose]

theorem masterNumeratorBCM1_eq_masterNumerator (A R δ f : ℕ) :
    masterNumeratorBCM1 A R δ f = masterNumerator A R δ f := by
  rw [masterNumeratorBCM1, masterNumerator,
    masterAlphaBCM1_eq_masterAlpha]

/-- Native source entry bound to the exact recurrence-kernel value route. -/
theorem entry_eq_masterNumeratorBCM1
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y)
    (hMleR : (mismatches i u y).card ≤ R) :
    entry i t A R u y =
      masterNumeratorBCM1 A R (activeSet i u).card
        ((mismatches i u y).card - 1) := by
  rw [masterNumeratorBCM1_eq_masterNumerator]
  exact entry_eq_masterNumerator i t A R u y horbit ht hMleR

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
