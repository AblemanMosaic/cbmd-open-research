import OAI.Algorithms.SubexponentialSAT.SqrtLog.EntryClosedFormSigned
import OAI.Algorithms.SubexponentialSAT.SqrtLog.EntryClosedFormCounting

/-!
# Assembly of the guarded entry closed form

The first theorem evaluates the fixed-cardinality inner sum in the pinned
`LayoutNumerator.entry` definition.  It combines active-subword uniqueness,
inactive-coordinate cancellation, and the guarded powerset count.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- The fixed-`j` inner sum in `entry` is a signed guarded binomial count. -/
theorem integerDifference_powerset_sum (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y) (j : ℕ) :
    (∑ S ∈ (activePositions t).powersetCard j,
      integerDifference i S.toList (integerDelta y)
        (swapPositions i (activePositions t) u)) =
      (-1 : ℤ) ^ ((mismatches i u y).erase t).card *
        (if (mismatches i u y).card - 1 ≤ j then
          ((activeSet i u).card - (mismatches i u y).card).choose
            (j - ((mismatches i u y).card - 1))
        else 0) := by
  classical
  let D := activeSet i u
  let M := mismatches i u y
  let T := M.erase t
  let L := activePositions t
  let sign : ℤ := (-1 : ℤ) ^ T.card
  have hMD : M ⊆ D := mismatches_subset_activeSet_of_inOrbit i u y horbit
  have hterm : ∀ S ∈ L.powersetCard j,
      integerDifference i S.toList (integerDelta y) (swapPositions i L u) =
        if S ⊆ D ∧ T ⊆ S then sign else 0 := by
    intro S hS
    have hSL : S ⊆ L := (Finset.mem_powersetCard.mp hS).1
    by_cases hSD : S ⊆ D
    · rw [integerDifference_active_subset i t u y horbit ht S hSL hSD]
      by_cases hTS : T ⊆ S
      · rw [if_pos hTS, if_pos ⟨hSD, hTS⟩]
      · rw [if_neg hTS, if_neg]
        exact fun h => hTS h.2
    · obtain ⟨a, haS, haD⟩ := Finset.not_subset.mp hSD
      have hzero := integerDifference_eq_zero_of_mem_not_activeSet i S.toList a
        (integerDelta y) L u (by simpa using haS) haD
      rw [hzero, if_neg]
      exact fun h => hSD h.1
  have hfilter :
      (L.powersetCard j).filter (fun S => S ⊆ D ∧ T ⊆ S) =
        ((D.erase t).powersetCard j).filter (T ⊆ ·) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hSL, hcard⟩, hSD, hTS⟩
      refine ⟨⟨?_, hcard⟩, hTS⟩
      intro x hxS
      refine Finset.mem_erase.mpr ⟨?_, hSD hxS⟩
      intro hxt
      subst x
      exact (Finset.mem_erase.mp (hSL hxS)).1 rfl
    · rintro ⟨⟨hSD, hcard⟩, hTS⟩
      refine ⟨⟨?_, hcard⟩, ?_, hTS⟩
      · intro x hxS
        have hxt : x ≠ t := (Finset.mem_erase.mp (hSD hxS)).1
        simp [L, activePositions, hxt]
      · intro x hxS
        exact (Finset.mem_erase.mp (hSD hxS)).2
  calc
    (∑ S ∈ L.powersetCard j,
      integerDifference i S.toList (integerDelta y) (swapPositions i L u)) =
        ∑ S ∈ L.powersetCard j,
          (if S ⊆ D ∧ T ⊆ S then sign else 0) := by
            apply Finset.sum_congr rfl
            intro S hS
            exact hterm S hS
    _ = (∑ S ∈ L.powersetCard j,
          (if S ⊆ D ∧ T ⊆ S then (1 : ℤ) else 0)) * sign := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro S _
            split_ifs <;> simp
    _ = (((L.powersetCard j).filter (fun S => S ⊆ D ∧ T ⊆ S)).card : ℤ) *
          sign := by simp
    _ = ((((D.erase t).powersetCard j).filter (T ⊆ ·)).card : ℤ) * sign := by
          rw [hfilter]
    _ = (if M.card - 1 ≤ j then
          (D.card - M.card).choose (j - (M.card - 1)) else 0) * sign := by
          rw [card_powersetCard_filter_erase_subset D M t j hMD ht]
    _ = sign * (if M.card - 1 ≤ j then
          (D.card - M.card).choose (j - (M.card - 1)) else 0) := by ring
    _ = (-1 : ℤ) ^ ((mismatches i u y).erase t).card *
        (if (mismatches i u y).card - 1 ≤ j then
          ((activeSet i u).card - (mismatches i u y).card).choose
            (j - ((mismatches i u y).card - 1)) else 0) := by rfl

/-- Guarded closed form for the pinned native integer entry.  The explicit
lower-index guard prevents the natural-subtraction error in the refuted first
candidate. -/
theorem entry_closed_form_guarded (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y) :
    entry i t A R u y =
      (-1 : ℤ) ^ ((mismatches i u y).erase t).card *
        ∑ j ∈ Finset.range R,
          extendCoefficients (parityCoefficients (K := ℤ) A R) j *
            2 ^ (R - 1 - j) *
              (if (mismatches i u y).card - 1 ≤ j then
                ((activeSet i u).card - (mismatches i u y).card).choose
                  (j - ((mismatches i u y).card - 1))
              else 0) := by
  unfold entry
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integerDifference_powerset_sum i t u y horbit ht j]
  ring

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
