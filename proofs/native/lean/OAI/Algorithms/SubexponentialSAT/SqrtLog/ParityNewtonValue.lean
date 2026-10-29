import OAI.Algorithms.SubexponentialSAT.SqrtLog.MasterAmplitudeBinomialBridge
import Mathlib.Data.Nat.Choose.Sum

/-!
# Newton value formula for the parity interpolant

This is the value-level first half of the closed-form parity-vector proof.  It
shows that the truncated forward-difference formula has exactly the prescribed
alternating values at every interpolation node.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset

/-- Truncated Newton interpolation of parity, written with the same executable
generalized coefficient used by `masterAlpha`. -/
def newtonParityValue (A R x : ℕ) : ℤ :=
  (-1 : ℤ) ^ A *
    ∑ k ∈ range R,
      (-2 : ℤ) ^ k * generalizedChoose ((x : ℤ) - A) k

theorem newtonParityValue_node (A R : ℕ) (d : Fin R) :
    newtonParityValue A R (A + d.val) =
      (-1 : ℤ) ^ (A + d.val) := by
  have harg : ((A + d.val : ℕ) : ℤ) - (A : ℤ) = (d.val : ℤ) := by
    omega
  have hsub : range (d.val + 1) ⊆ range R := by
    intro k hk
    simp only [mem_range] at hk ⊢
    omega
  have htruncate :
      (∑ k ∈ range R, (-2 : ℤ) ^ k * (d.val.choose k : ℤ)) =
        ∑ k ∈ range (d.val + 1),
          (-2 : ℤ) ^ k * (d.val.choose k : ℤ) := by
    symm
    apply Finset.sum_subset hsub
    intro k hkR hkSmall
    have hdk : d.val < k := by
      simp only [mem_range, not_lt] at hkSmall
      omega
    rw [Nat.choose_eq_zero_of_lt hdk, Nat.cast_zero, mul_zero]
  rw [newtonParityValue, harg]
  simp_rw [generalizedChoose_eq_ringChoose,
    Ring.choose_natCast (R := ℤ)]
  rw [htruncate]
  have hbinomial := add_pow (-2 : ℤ) 1 d.val
  simp only [one_pow, mul_one] at hbinomial
  have hsum :
      (∑ k ∈ range (d.val + 1),
          (-2 : ℤ) ^ k * (d.val.choose k : ℤ)) =
        (-1 : ℤ) ^ d.val := by
    rw [← hbinomial]
    norm_num
  calc
    (-1 : ℤ) ^ A *
        ∑ k ∈ range (d.val + 1),
          (-2 : ℤ) ^ k * (d.val.choose k : ℤ) =
      (-1 : ℤ) ^ A * (-1 : ℤ) ^ d.val := by
        rw [hsum]
    _ = (-1 : ℤ) ^ (A + d.val) := by rw [pow_add]

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
