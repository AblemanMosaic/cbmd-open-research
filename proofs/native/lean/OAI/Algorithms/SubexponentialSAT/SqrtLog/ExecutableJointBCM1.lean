import OAI.Algorithms.SubexponentialSAT.SqrtLog.BCM1CostSemantics

/-!
# Total executable candidate for the joint numerator matrix

The source's `entry`, `joint`, and `family` are noncomputable theorem-level
definitions.  This module closes the value domain for one joint matrix:

* outside the selected-slot swap orbit, the literal entry is zero;
* above the mismatch support bound, the literal entry is zero;
* on the remaining cells, the counted BCM-1 kernel gives the entry.

The Boolean orbit test deliberately enumerates the powerset.  It is a portable
correctness realization, not an optimized or charged orbit test.  Consequently
the module establishes total executable value correspondence, not a total-cost
speedup.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- Swap-orbit membership is closed under one further swap. -/
theorem inOrbit_swapPositions (i : Fin Δ) (u v : UniversalType r Q Δ)
    (hv : InOrbit i u v) (b : Finset (Fin Q)) :
    InOrbit i u (swapPositions i b v) := by
  obtain ⟨s, rfl⟩ := hv
  refine ⟨(s \ b) ∪ (b \ s), ?_⟩
  apply UniversalType.ext
  · funext l
    by_cases hs : l ∈ s <;> by_cases hb : l ∈ b <;> simp [hs, hb]
  · funext j l
    by_cases hji : j = i
    · subst j
      by_cases hs : l ∈ s <;> by_cases hb : l ∈ b <;> simp [hs, hb]
    · simp [swapPositions_slot_other, hji]

theorem integerDelta_eq_zero_of_not_inOrbit
    (i : Fin Δ) (u y v : UniversalType r Q Δ)
    (hy : ¬ InOrbit i u y) (hv : InOrbit i u v) :
    integerDelta y v = 0 := by
  rw [integerDelta]
  split_ifs with h
  · subst v
    exact (hy hv).elim
  · rfl

theorem integerDifference_delta_eq_zero_of_not_inOrbit
    (i : Fin Δ) (u y v : UniversalType r Q Δ)
    (hy : ¬ InOrbit i u y) (hv : InOrbit i u v) :
    ∀ as : List (Fin Q), integerDifference i as (integerDelta y) v = 0 := by
  intro as
  induction as generalizing v with
  | nil => exact integerDelta_eq_zero_of_not_inOrbit i u y v hy hv
  | cons a as ih =>
      rw [integerDifference, ih v hv,
        ih (swapPositions i {a} v)
          (inOrbit_swapPositions i u v hv {a})]
      norm_num

/-- The literal source entry has no support outside the swap orbit. -/
theorem entry_eq_zero_of_not_inOrbit
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) (hy : ¬ InOrbit i u y) :
    entry i t A R u y = 0 := by
  unfold entry
  apply Finset.sum_eq_zero
  intro j hj
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro S hS
  apply integerDifference_delta_eq_zero_of_not_inOrbit i u y
  · exact hy
  · exact ⟨activePositions t, rfl⟩

/-- Universal support theorem for the integer source entry. -/
theorem entry_support (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) (hne : entry i t A R u y ≠ 0) :
    (mismatches i u y).card ≤ R := by
  apply matrixEntry_support i t R
    (extendCoefficients (parityCoefficients (K := ℚ) A R)) u y
  intro hz
  have hc := entry_cast ℚ (by norm_num) i t A R u y
  rw [hz, mul_zero] at hc
  exact hne (by exact_mod_cast hc)

theorem entry_eq_zero_of_mismatch_card_gt
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (hgt : R < (mismatches i u y).card) :
    entry i t A R u y = 0 := by
  by_contra hne
  have := entry_support i t A R u y hne
  omega

/-- A finite-function presentation of orbit membership, used to obtain a
computable decision procedure without choosing an ordering of finsets. -/
def OrbitBits (i : Fin Δ) (u y : UniversalType r Q Δ) : Prop :=
  ∃ bits : Fin Q → Bool,
    y = swapPositions i (Finset.univ.filter (fun l => bits l)) u

theorem orbitBits_iff_inOrbit (i : Fin Δ) (u y : UniversalType r Q Δ) :
    OrbitBits i u y ↔ InOrbit i u y := by
  constructor
  · rintro ⟨bits, h⟩
    exact ⟨Finset.univ.filter (fun l => bits l), h⟩
  · rintro ⟨s, h⟩
    refine ⟨fun l => decide (l ∈ s), ?_⟩
    convert h using 1
    congr 1
    ext l
    simp

def orbitBitsDecidable (i : Fin Δ) (u y : UniversalType r Q Δ) :
    Decidable (OrbitBits i u y) :=
  Fintype.decidableExistsFintype

/-- Executable orbit predicate.  The finite Boolean-function search is
intentional and is not included in the scalar BCM-1 charge. -/
def inOrbitB (i : Fin Δ) (u y : UniversalType r Q Δ) : Bool :=
  @decide (OrbitBits i u y) (orbitBitsDecidable i u y)

theorem inOrbitB_eq_true_iff (i : Fin Δ) (u y : UniversalType r Q Δ) :
    inOrbitB i u y = true ↔ InOrbit i u y := by
  simp [inOrbitB, orbitBits_iff_inOrbit]

/-- Total counted candidate for one cell of the joint integer numerator
matrix.  Zero branches carry no scalar arithmetic charge. -/
def jointEntryBCM1Total (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    {g : Fin r} (u y : Joint t g i) : BCM1Costed ℤ :=
  if inOrbitB i u.val y.val then
    if (mismatches i u.val y.val).card ≤ R then
      masterNumeratorBCM1Costed A R (activeSet i u.val).card
        ((mismatches i u.val y.val).card - 1)
    else ⟨0, ⟨0, 0, 0⟩⟩
  else ⟨0, ⟨0, 0, 0⟩⟩

theorem jointEntryBCM1Total_value
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ)
    (u y : Joint t g i) :
    (jointEntryBCM1Total i t A R u y).value = joint i t g A R u y := by
  rw [joint]
  by_cases horbitB : inOrbitB i u.val y.val
  · have horbit : InOrbit i u.val y.val :=
      (inOrbitB_eq_true_iff i u.val y.val).mp horbitB
    by_cases hcard : (mismatches i u.val y.val).card ≤ R
    · simp [jointEntryBCM1Total, horbitB, hcard,
        masterNumeratorBCM1Costed_value]
      exact (entry_eq_masterNumeratorBCM1 i t A R u.val y.val horbit
        (joint_mismatch_at_t i t g u y) hcard).symm
    · have hgt : R < (mismatches i u.val y.val).card := by omega
      simp [jointEntryBCM1Total, horbitB, hcard,
        entry_eq_zero_of_mismatch_card_gt i t A R u.val y.val hgt]
  · have horbit : ¬ InOrbit i u.val y.val := by
      intro h
      exact horbitB ((inOrbitB_eq_true_iff i u.val y.val).mpr h)
    simp [jointEntryBCM1Total, horbitB,
      entry_eq_zero_of_not_inOrbit i t A R u.val y.val horbit]

/-- Total executable value matrix corresponding to the source `joint`. -/
def jointBCM1Total (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    Matrix (Joint t g i) (Joint t g i) ℤ :=
  fun u y => (jointEntryBCM1Total i t A R u y).value

theorem jointBCM1Total_eq_joint
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    jointBCM1Total i t g A R = joint i t g A R := by
  ext u y
  exact jointEntryBCM1Total_value i t g A R u y

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
