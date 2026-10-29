import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutableJointBCM1

/-!
# Coordinatewise orbit recognition

The exhaustive orbit decider is replaced by a local characterization: all
unselected slots are unchanged, and at each coordinate the `(head,slot i)`
pair is either unchanged or swapped.  This removes the `2^Q` search from the
total executable joint candidate.

Only value correspondence is proved here.  Equality-comparison and
short-circuit costs are a separate declared-model obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

def OrbitCompatible (i : Fin Δ) (u y : UniversalType r Q Δ) : Prop :=
  (∀ j : Fin Δ, j ≠ i → ∀ l : Fin Q, y.slot j l = u.slot j l) ∧
  (∀ l : Fin Q,
    (y.head l = u.head l ∧ y.slot i l = u.slot i l) ∨
    (y.head l = u.slot i l ∧ y.slot i l = u.head l))

theorem inOrbit_iff_orbitCompatible
    (i : Fin Δ) (u y : UniversalType r Q Δ) :
    InOrbit i u y ↔ OrbitCompatible i u y := by
  constructor
  · rintro ⟨s, rfl⟩
    constructor
    · intro j hji l
      exact swapPositions_slot_other i j hji s u l
    · intro l
      by_cases hl : l ∈ s
      · right
        simp [hl]
      · left
        simp [hl]
  · rintro ⟨hother, hpairs⟩
    let s : Finset (Fin Q) := Finset.univ.filter fun l =>
      y.head l = u.slot i l ∧ y.slot i l = u.head l
    refine ⟨s, ?_⟩
    apply UniversalType.ext
    · funext l
      rcases hpairs l with hsame | hswap
      · by_cases hl : l ∈ s
        · have hs : y.head l = u.slot i l ∧ y.slot i l = u.head l := by
            simpa [s] using hl
          have hu : u.head l = u.slot i l := hsame.1.symm.trans hs.1
          simp [swapPositions_head, hl, hsame.1, hu]
        · simp [swapPositions_head, hl, hsame.1]
      · have hl : l ∈ s := by simpa [s] using hswap
        simp [swapPositions_head, hl, hswap.1]
    · funext j l
      by_cases hji : j = i
      · subst j
        rcases hpairs l with hsame | hswap
        · by_cases hl : l ∈ s
          · have hs : y.head l = u.slot i l ∧ y.slot i l = u.head l := by
              simpa [s] using hl
            have hu : u.slot i l = u.head l := hsame.2.symm.trans hs.2
            simp [swapPositions_slot_same, hl, hsame.2, hu]
          · simp [swapPositions_slot_same, hl, hsame.2]
        · have hl : l ∈ s := by simpa [s] using hswap
          simp [swapPositions_slot_same, hl, hswap.2]
      · rw [swapPositions_slot_other i j hji]
        exact hother j hji l

def orbitCompatibleDecidable
    (i : Fin Δ) (u y : UniversalType r Q Δ) :
    Decidable (OrbitCompatible i u y) := by
  unfold OrbitCompatible
  letI : ∀ j : Fin Δ,
      Decidable (∀ l : Fin Q, y.slot j l = u.slot j l) :=
    fun _ => Fintype.decidableForallFintype
  letI : ∀ j : Fin Δ,
      Decidable (j ≠ i → ∀ l : Fin Q, y.slot j l = u.slot j l) :=
    fun _ => inferInstance
  letI : Decidable
      (∀ j : Fin Δ, j ≠ i → ∀ l : Fin Q, y.slot j l = u.slot j l) :=
    Fintype.decidableForallFintype
  letI : ∀ l : Fin Q, Decidable
      ((y.head l = u.head l ∧ y.slot i l = u.slot i l) ∨
       (y.head l = u.slot i l ∧ y.slot i l = u.head l)) :=
    fun _ => inferInstance
  letI : Decidable
      (∀ l : Fin Q,
        (y.head l = u.head l ∧ y.slot i l = u.slot i l) ∨
        (y.head l = u.slot i l ∧ y.slot i l = u.head l)) :=
    Fintype.decidableForallFintype
  infer_instance

def orbitCompatibleB (i : Fin Δ) (u y : UniversalType r Q Δ) : Bool :=
  @decide (OrbitCompatible i u y) (orbitCompatibleDecidable i u y)

theorem orbitCompatibleB_eq_true_iff
    (i : Fin Δ) (u y : UniversalType r Q Δ) :
    orbitCompatibleB i u y = true ↔ InOrbit i u y := by
  letI : Decidable (OrbitCompatible i u y) := orbitCompatibleDecidable i u y
  rw [orbitCompatibleB, decide_eq_true_eq, inOrbit_iff_orbitCompatible]

/-- Total counted joint-cell candidate using the coordinatewise orbit test. -/
def jointEntryBCM1Coordinate (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    {g : Fin r} (u y : Joint t g i) : BCM1Costed ℤ :=
  if orbitCompatibleB i u.val y.val then
    if (mismatches i u.val y.val).card ≤ R then
      masterNumeratorBCM1Costed A R (activeSet i u.val).card
        ((mismatches i u.val y.val).card - 1)
    else ⟨0, ⟨0, 0, 0⟩⟩
  else ⟨0, ⟨0, 0, 0⟩⟩

theorem jointEntryBCM1Coordinate_value
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ)
    (u y : Joint t g i) :
    (jointEntryBCM1Coordinate i t A R u y).value =
      joint i t g A R u y := by
  rw [joint]
  by_cases horbitB : orbitCompatibleB i u.val y.val
  · have horbit : InOrbit i u.val y.val :=
      (orbitCompatibleB_eq_true_iff i u.val y.val).mp horbitB
    by_cases hcard : (mismatches i u.val y.val).card ≤ R
    · simp [jointEntryBCM1Coordinate, horbitB, hcard,
        masterNumeratorBCM1Costed_value]
      exact (entry_eq_masterNumeratorBCM1 i t A R u.val y.val horbit
        (joint_mismatch_at_t i t g u y) hcard).symm
    · have hgt : R < (mismatches i u.val y.val).card := by omega
      simp [jointEntryBCM1Coordinate, horbitB, hcard,
        entry_eq_zero_of_mismatch_card_gt i t A R u.val y.val hgt]
  · have horbit : ¬ InOrbit i u.val y.val := by
      intro h
      exact horbitB ((orbitCompatibleB_eq_true_iff i u.val y.val).mpr h)
    simp [jointEntryBCM1Coordinate, horbitB,
      entry_eq_zero_of_not_inOrbit i t A R u.val y.val horbit]

def jointBCM1Coordinate (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    Matrix (Joint t g i) (Joint t g i) ℤ :=
  fun u y => (jointEntryBCM1Coordinate i t A R u y).value

theorem jointBCM1Coordinate_eq_joint
    (i : Fin Δ) (t : Fin Q) (g : Fin r) (A R : ℕ) :
    jointBCM1Coordinate i t g A R = joint i t g A R := by
  ext u y
  exact jointEntryBCM1Coordinate_value i t g A R u y

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
