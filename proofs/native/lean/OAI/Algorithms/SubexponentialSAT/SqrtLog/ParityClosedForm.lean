import OAI.Algorithms.SubexponentialSAT.SqrtLog.ParityNewtonPolynomial
import Mathlib.RingTheory.Binomial

/-!
# Closed-form boundary for the parity coefficients

The first step is the exact Chu--Vandermonde convolution that removes the
shift by `A`.  It is stated over `ℤ`, matching the native coefficient ring.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset

theorem choose_int_convolution (a b : ℤ) (k : ℕ) :
    (∑ n ∈ range (k + 1),
        Ring.choose a n * Ring.choose b (k - n)) =
      Ring.choose (a + b) k := by
  calc
    (∑ n ∈ range (k + 1),
        Ring.choose a n * Ring.choose b (k - n)) =
        ∑ ij ∈ antidiagonal k,
          Ring.choose a ij.1 * Ring.choose b ij.2 := by
            rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = Ring.choose (a + b) k :=
      (Ring.add_choose_eq (R := ℤ) k (Commute.all _ _)).symm

theorem choose_shift_convolution (A d k : ℕ) :
    (∑ n ∈ range (k + 1),
        Ring.choose (-(A : ℤ)) n *
          Ring.choose ((A + d : ℕ) : ℤ) (k - n)) =
      Ring.choose (d : ℤ) k := by
  have hadd : -(A : ℤ) + ((A + d : ℕ) : ℤ) = (d : ℤ) := by
    norm_num
  rw [choose_int_convolution, hadd]

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
