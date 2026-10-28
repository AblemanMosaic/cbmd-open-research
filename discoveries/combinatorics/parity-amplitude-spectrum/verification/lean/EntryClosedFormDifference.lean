import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
import OAI.Algorithms.SubexponentialSAT.SqrtLog.EntryClosedFormOrbit

/-!
# Difference expansion for the entry closed-form bridge

This file gives the exact integer signed-subset expansion and connects native
Kronecker deltas on two orbit states to agreement on active coordinates.  It
does not import the admitted centered-vanishing module.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- The ordered integer difference is the signed sum over all subwords. -/
theorem integerDifference_expansion (i : Fin Δ) (as : List (Fin Q))
    (f : UniversalType r Q Δ → ℤ) (u : UniversalType r Q Δ) :
    integerDifference i as f u =
      (as.sublists'.map (fun bs =>
        (-1 : ℤ) ^ bs.length * f (applySwaps i bs u))).sum := by
  induction as generalizing u with
  | nil => simp [integerDifference, applySwaps]
  | cons a as ih =>
    simp only [integerDifference, ih, List.sublists'_cons, List.map_append,
      List.sum_append, List.map_map, Function.comp_def, List.length_cons,
      applySwaps, pow_succ]
    simp only [mul_assoc, mul_comm (-1 : ℤ)]
    simp only [← mul_assoc]
    rw [List.sum_map_mul_right]
    ring

/-- If one coordinate in an ordered difference fixes the evaluation point,
the whole difference vanishes.  Commutativity of position swaps propagates
the fixed-point property through the remaining factors. -/
theorem integerDifference_eq_zero_of_mem_of_swap_fixed (i : Fin Δ)
    (as : List (Fin Q)) (a : Fin Q) (f : UniversalType r Q Δ → ℤ)
    (u : UniversalType r Q Δ) (ha : a ∈ as)
    (hfixed : swapPositions i {a} u = u) :
    integerDifference i as f u = 0 := by
  induction as generalizing u with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp [integerDifference, hfixed]
    · have hfixed' :
          swapPositions i {a} (swapPositions i {b} u) =
            swapPositions i {b} u := by
        rw [swapPositions_commute, hfixed]
      rw [integerDifference, ih u ha hfixed,
        ih (swapPositions i {b} u) ha hfixed', sub_self]

/-- Any difference list containing a coordinate inactive in the source state
vanishes at every point in that source's swap orbit. -/
theorem integerDifference_eq_zero_of_mem_not_activeSet (i : Fin Δ)
    (as : List (Fin Q)) (a : Fin Q) (f : UniversalType r Q Δ → ℤ)
    (L : Finset (Fin Q)) (u : UniversalType r Q Δ) (ha : a ∈ as)
    (hinactive : a ∉ activeSet i u) :
    integerDifference i as f (swapPositions i L u) = 0 := by
  apply integerDifference_eq_zero_of_mem_of_swap_fixed i as a f _ ha
  rw [swapPositions_commute,
    swapPositions_singleton_eq_self_of_not_mem_activeSet i a u hinactive]

/-- Native integer delta between two orbit states depends only on their swap
sets restricted to active coordinates. -/
theorem integerDelta_swapPositions (i : Fin Δ) (a b : Finset (Fin Q))
    (u : UniversalType r Q Δ) :
    integerDelta (swapPositions i a u) (swapPositions i b u) =
      if a ∩ activeSet i u = b ∩ activeSet i u then 1 else 0 := by
  unfold integerDelta
  simp only [swapPositions_eq_iff_inter_activeSet]
  by_cases h : a ∩ activeSet i u = b ∩ activeSet i u
  · rw [if_pos h.symm, if_pos h]
  · have hsymm : b ∩ activeSet i u ≠ a ∩ activeSet i u := Ne.symm h
    rw [if_neg hsymm, if_neg h]

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
