import OAI.Algorithms.SubexponentialSAT.SqrtLog.MasterNumeratorBCM1

/-!
# Kernel-checked BCM-1 arithmetic counts

The counted recurrences below pair every recursive value step with its declared
BCM-1 arithmetic charge.  The final convolution has `d+1` explicit products
and additions, followed by one scale multiplication.  This proves the exact
arithmetic-operation vector for the admitted kernel.

This is not a machine-cost model: allocation, indexing, traversal, unary sign
changes, exponent construction, and bit complexity remain outside the count.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

structure BCM1Counts where
  mul : ℕ
  div : ℕ
  add : ℕ
deriving DecidableEq, Repr

structure BCM1Costed (X : Type) where
  value : X
  counts : BCM1Counts
deriving Repr

/-- Counted generalized-binomial recurrence.  Each successor step contains
one multiplication and one exact division. -/
def generalizedChooseRevCosted (N : ℤ) : ℕ → BCM1Costed (List ℤ)
  | 0 => ⟨[1], ⟨0, 0, 0⟩⟩
  | d + 1 =>
      let previous := generalizedChooseRevCosted N d
      let next := previous.value.headD 0 * (N - (d : ℤ)) /
        ((d + 1 : ℕ) : ℤ)
      ⟨next :: previous.value,
        ⟨previous.counts.mul + 1, previous.counts.div + 1,
          previous.counts.add⟩⟩

theorem generalizedChooseRevCosted_value (N : ℤ) : ∀ d : ℕ,
    (generalizedChooseRevCosted N d).value = generalizedChooseRev N d := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih => simp [generalizedChooseRevCosted, generalizedChooseRev, ih]

theorem generalizedChooseRevCosted_counts (N : ℤ) : ∀ d : ℕ,
    (generalizedChooseRevCosted N d).counts = ⟨d, d, 0⟩ := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [generalizedChooseRevCosted]
      simp only [ih]

/-- Counted direct negative-binomial recurrence, with the same one-multiply,
one-exact-division charge at every successor step. -/
def negativeBinomialRevBCM1Costed (A : ℕ) : ℕ → BCM1Costed (List ℤ)
  | 0 => ⟨[1], ⟨0, 0, 0⟩⟩
  | d + 1 =>
      let previous := negativeBinomialRevBCM1Costed A d
      let next := previous.value.headD 0 * ((A + d : ℕ) : ℤ) /
        ((d + 1 : ℕ) : ℤ)
      ⟨next :: previous.value,
        ⟨previous.counts.mul + 1, previous.counts.div + 1,
          previous.counts.add⟩⟩

theorem negativeBinomialRevBCM1Costed_value (A : ℕ) : ∀ d : ℕ,
    (negativeBinomialRevBCM1Costed A d).value =
      negativeBinomialRevBCM1 A d := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      simp [negativeBinomialRevBCM1Costed, negativeBinomialRevBCM1, ih]

theorem negativeBinomialRevBCM1Costed_counts (A : ℕ) : ∀ d : ℕ,
    (negativeBinomialRevBCM1Costed A d).counts = ⟨d, d, 0⟩ := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [negativeBinomialRevBCM1Costed]
      simp only [ih]

/-- Counted value semantics for the exact BCM-1 kernel.  The two recurrence
tables are each evaluated once and let-bound before the convolution. -/
def masterNumeratorBCM1Costed (A R δ f : ℕ) : BCM1Costed ℤ :=
  let d := R - 1 - f
  let chooseRev := generalizedChooseRevCosted
    ((A : ℤ) + (R : ℤ) - (δ : ℤ)) d
  let negativeRev := negativeBinomialRevBCM1Costed A d
  let total := ∑ k ∈ range (d + 1),
    chooseRev.value.reverse.getD k 0 *
      negativeRev.value.reverse.getD (d - k) 0
  ⟨2 ^ (R - 1) * applyParitySign A total,
    ⟨chooseRev.counts.mul + negativeRev.counts.mul + (d + 1) + 1,
      chooseRev.counts.div + negativeRev.counts.div,
      chooseRev.counts.add + negativeRev.counts.add + (d + 1)⟩⟩

theorem masterNumeratorBCM1Costed_value (A R δ f : ℕ) :
    (masterNumeratorBCM1Costed A R δ f).value =
      masterNumeratorBCM1 A R δ f := by
  simp [masterNumeratorBCM1Costed, masterNumeratorBCM1, masterAlphaBCM1,
    generalizedChooseTable, negativeBinomialTableBCM1,
    generalizedChooseRevCosted_value, negativeBinomialRevBCM1Costed_value]

/-- Exact BCM-1 arithmetic-operation vector for the admitted kernel. -/
theorem masterNumeratorBCM1Costed_counts (A R δ f : ℕ) :
    (masterNumeratorBCM1Costed A R δ f).counts =
      ⟨3 * (R - 1 - f) + 2, 2 * (R - 1 - f), (R - 1 - f) + 1⟩ := by
  simp [masterNumeratorBCM1Costed, generalizedChooseRevCosted_counts,
    negativeBinomialRevBCM1Costed_counts]
  constructor <;> omega

theorem masterNumeratorBCM1Costed_mul_le (A R δ f : ℕ) (hf : f < R) :
    (masterNumeratorBCM1Costed A R δ f).counts.mul ≤ 3 * R - 1 := by
  rw [masterNumeratorBCM1Costed_counts]
  change 3 * (R - 1 - f) + 2 ≤ 3 * R - 1
  omega

theorem masterNumeratorBCM1Costed_div_le (A R δ f : ℕ) (hf : f < R) :
    (masterNumeratorBCM1Costed A R δ f).counts.div ≤ 2 * R - 2 := by
  rw [masterNumeratorBCM1Costed_counts]
  change 2 * (R - 1 - f) ≤ 2 * R - 2
  omega

theorem masterNumeratorBCM1Costed_add_le (A R δ f : ℕ) (hf : f < R) :
    (masterNumeratorBCM1Costed A R δ f).counts.add ≤ R := by
  rw [masterNumeratorBCM1Costed_counts]
  change (R - 1 - f) + 1 ≤ R
  omega

/-- The counted kernel's value is the native source entry under the same
orbit/mismatch hypotheses as the uncounted bridge. -/
theorem entry_eq_masterNumeratorBCM1Costed_value
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y)
    (hMleR : (mismatches i u y).card ≤ R) :
    entry i t A R u y =
      (masterNumeratorBCM1Costed A R (activeSet i u).card
        ((mismatches i u y).card - 1)).value := by
  rw [masterNumeratorBCM1Costed_value]
  exact entry_eq_masterNumeratorBCM1 i t A R u y horbit ht hMleR

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
