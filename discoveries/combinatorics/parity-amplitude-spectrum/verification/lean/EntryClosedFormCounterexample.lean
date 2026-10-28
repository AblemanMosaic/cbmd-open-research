import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

/-!
# Counterexample to the first `entry_closed_form` candidate

This file does not import the workbench module containing admitted transport
statements.  It evaluates the pinned native definitions directly.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport

def counterU : UniversalType 2 2 1 where
  head := fun _ => 0
  slot := fun _ _ => 1

def counterI : Fin 1 := 0
def counterT : Fin 2 := 0

def counterActiveSet : Finset (Fin 2) :=
  Finset.univ.filter (fun l => counterU.head l ≠ counterU.slot counterI l)

theorem counter_in_orbit :
    ∃ s : Finset (Fin 2), counterU = swapPositions counterI s counterU := by
  exact ⟨∅, (swapPositions_empty counterI counterU).symm⟩

theorem counter_t_mismatch :
    counterT ∈ mismatches counterI counterU counterU := by
  native_decide

theorem counter_cards :
    counterActiveSet.card = 2 ∧
      (mismatches counterI counterU counterU).card = 2 := by
  native_decide

theorem counter_entry :
    entry counterI counterT 0 1 counterU counterU = 0 := by
  have hswap :
      swapPositions counterI (activePositions counterT) counterU ≠ counterU := by
    native_decide
  have hdelta :
      integerDelta counterU
        (swapPositions counterI (activePositions counterT) counterU) = 0 := by
    simp [integerDelta, hswap]
  simp [entry, integerDifference, hdelta]

theorem counter_candidate_rhs :
    (-1 : ℤ) ^ ((mismatches counterI counterU counterU).card - 1) *
      ∑ j ∈ Finset.range 1,
        extendCoefficients (parityCoefficients (K := ℤ) 0 1) j *
          2 ^ (1 - 1 - j) *
            ((counterActiveSet.card - (mismatches counterI counterU counterU).card).choose
              (j - ((mismatches counterI counterU counterU).card - 1)) : ℤ) = -1 := by
  have h := sum_range_extend_parity (K := ℤ) 0 1 ⟨0, by omega⟩
  norm_num [counterActiveSet, counterU, counterI, mismatches] at h ⊢
  exact h

theorem entry_closed_form_candidate_is_false :
    entry counterI counterT 0 1 counterU counterU ≠
      (-1 : ℤ) ^ ((mismatches counterI counterU counterU).card - 1) *
        ∑ j ∈ Finset.range 1,
          extendCoefficients (parityCoefficients (K := ℤ) 0 1) j *
            2 ^ (1 - 1 - j) *
              ((counterActiveSet.card - (mismatches counterI counterU counterU).card).choose
                (j - ((mismatches counterI counterU counterU).card - 1)) : ℤ) := by
  rw [counter_entry, counter_candidate_rhs]
  norm_num

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
