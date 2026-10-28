import OAI.Algorithms.SubexponentialSAT.SqrtLog.EntryClosedFormDifference

/-!
# Unique active subword for the entry closed-form bridge

This file identifies the exact active swap subset that sends the fully
complemented base point to a target in the source swap orbit.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- Among subsets of the non-pivot coordinates, equality with the target is
equivalent to selecting exactly the non-pivot mismatches on active positions. -/
theorem swap_activePositions_eq_target_iff (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y) (B : Finset (Fin Q))
    (hB : B ⊆ activePositions t) :
    swapPositions i B (swapPositions i (activePositions t) u) = y ↔
      B ∩ activeSet i u = (mismatches i u y).erase t := by
  obtain ⟨s, rfl⟩ := horbit
  have ht' : t ∈ activeSet i u \ s := by simpa using ht
  have htD : t ∈ activeSet i u := (Finset.mem_sdiff.mp ht').1
  have hts : t ∉ s := (Finset.mem_sdiff.mp ht').2
  have htB : t ∉ B := by
    intro htb
    have := hB htb
    simpa [activePositions] using this
  rw [swapPositions_sdiff i (activePositions t) B hB,
    swapPositions_eq_iff_inter_activeSet]
  rw [mismatches_swapPositions]
  constructor
  · intro h
    ext l
    have hl := Finset.ext_iff.mp h l
    by_cases hlt : l = t
    · subst l
      simp [htB]
    · have hlactive : l ∈ activePositions t := by simp [activePositions, hlt]
      simp only [Finset.mem_inter, Finset.mem_erase, Finset.mem_sdiff]
      simp [hlactive, hlt] at hl
      tauto
  · intro h
    ext l
    have hl := Finset.ext_iff.mp h l
    by_cases hlt : l = t
    · subst l
      simp [activePositions, htB, htD, hts]
    · have hlactive : l ∈ activePositions t := by simp [activePositions, hlt]
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      simp [hlt] at hl
      simp [hlactive]
      tauto

/-- A duplicate-free list of active non-pivot swaps contributes to the native
delta exactly when its underlying set is the non-pivot mismatch set. -/
theorem integerDelta_applySwaps_active (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y) (bs : List (Fin Q))
    (hbs : bs.Nodup) (hpos : bs.toFinset ⊆ activePositions t)
    (hactive : bs.toFinset ⊆ activeSet i u) :
    integerDelta y
        (applySwaps i bs (swapPositions i (activePositions t) u)) =
      if bs.toFinset = (mismatches i u y).erase t then 1 else 0 := by
  rw [applySwaps_eq_swapPositions i bs hbs]
  have hinter : bs.toFinset ∩ activeSet i u = bs.toFinset :=
    Finset.inter_eq_left.mpr hactive
  have hEq :
      swapPositions i bs.toFinset
          (swapPositions i (activePositions t) u) = y ↔
        bs.toFinset = (mismatches i u y).erase t := by
    simpa [hinter] using
      (swap_activePositions_eq_target_iff i t u y horbit ht bs.toFinset hpos)
  unfold integerDelta
  by_cases htarget : bs.toFinset = (mismatches i u y).erase t
  · rw [if_pos (hEq.mpr htarget), if_pos htarget]
  · rw [if_neg (fun h => htarget (hEq.mp h)), if_neg htarget]

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
