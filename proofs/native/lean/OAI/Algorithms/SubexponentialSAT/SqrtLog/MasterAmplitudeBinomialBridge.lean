import OAI.Algorithms.SubexponentialSAT.SqrtLog.NativeAmplitudeCostBridge
import Mathlib.RingTheory.Binomial

/-!
# Master-amplitude binomial bridge

The executable generalized coefficient used by the Batch 5 master formula is
identified with Mathlib's binomial-ring coefficient.  This makes the existing
Chu--Vandermonde library available for the remaining scalar proof.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

theorem generalizedChoose_eq_ringChoose (n : ℤ) (k : ℕ) :
    generalizedChoose n k = Ring.choose n k := by
  rfl

theorem negativeBinomialCoeff_eq_multichoose (A k : ℕ) :
    negativeBinomialCoeff A k = Ring.multichoose (A : ℤ) k := by
  rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
