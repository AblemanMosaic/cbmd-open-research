import OAI.Algorithms.SubexponentialSAT.SqrtLog.CenteredUmbralBridge
import OAI.Algorithms.SubexponentialSAT.SqrtLog.EntryClosedFormAssemble

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixSupport
noncomputable section

variable {r Q Δ : ℕ}

/-- Native centered vanishing stated at the reflection exponent used by the
integral umbral proof. -/
theorem entry_centered_vanishes_of_exponent_odd
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y)
    (hR : 1 ≤ R)
    (hcenter : (activeSet i u).card = 2 * A + R)
    (hodd : Odd ((R - 1) + ((mismatches i u y).card - 1))) :
    entry i t A R u y = 0 := by
  have hMD : mismatches i u y ⊆ activeSet i u :=
    mismatches_subset_activeSet_of_inOrbit i u y horbit
  have hMpos : 1 ≤ (mismatches i u y).card :=
    Finset.one_le_card.mpr ⟨t, ht⟩
  have hMle : (mismatches i u y).card ≤ (activeSet i u).card :=
    Finset.card_le_card hMD
  have hdegree :
      ((mismatches i u y).card - 1) +
          ((activeSet i u).card - (mismatches i u y).card) =
        2 * A + R - 1 := by
    omega
  rw [entry_closed_form_guarded i t A R u y horbit ht]
  simp only [Nat.cast_ite, Nat.cast_zero]
  change (-1 : ℤ) ^ ((mismatches i u y).erase t).card *
      centeredAmplitude A R
        ((mismatches i u y).card - 1)
        ((activeSet i u).card - (mismatches i u y).card) = 0
  rw [centeredAmplitude_eq_zero A R
    ((mismatches i u y).card - 1)
    ((activeSet i u).card - (mismatches i u y).card)
    hR hdegree hodd, mul_zero]

/-- Source-facing form of native centered vanishing: at centered active-set
cardinality, every orbit entry with `R - |E|` odd vanishes integrally. -/
theorem entry_centered_vanishes
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y)
    (hMleR : (mismatches i u y).card ≤ R)
    (hR : 1 ≤ R)
    (hcenter : (activeSet i u).card = 2 * A + R)
    (hparity : Odd (R - (mismatches i u y).card)) :
    entry i t A R u y = 0 := by
  have hMpos : 1 ≤ (mismatches i u y).card :=
    Finset.one_le_card.mpr ⟨t, ht⟩
  have hexponent :
      (R - 1) + ((mismatches i u y).card - 1) =
        (R - (mismatches i u y).card) +
          2 * ((mismatches i u y).card - 1) := by
    omega
  have hodd : Odd ((R - 1) + ((mismatches i u y).card - 1)) := by
    rw [hexponent]
    exact hparity.add_even (even_two_mul _)
  exact entry_centered_vanishes_of_exponent_odd
    i t A R u y horbit ht hR hcenter hodd

/-- Exact source-workbench parity form: `R + |E|` odd is equivalent to the
subtractive parity condition when `|E| ≤ R`. -/
theorem entry_eq_zero_of_centered_compiled
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (hR : 1 ≤ R) (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (hcentered : (activeSet i u).card = 2 * A + R)
    (ht : t ∈ mismatches i u y)
    (hle : (mismatches i u y).card ≤ R)
    (hodd : Odd (R + (mismatches i u y).card)) :
    entry i t A R u y = 0 := by
  have hdecomp :
      R + (mismatches i u y).card =
        (R - (mismatches i u y).card) +
          2 * (mismatches i u y).card := by
    omega
  have hadd : Odd ((R - (mismatches i u y).card) +
      2 * (mismatches i u y).card) := by
    simpa only [hdecomp] using hodd
  have hparity : Odd (R - (mismatches i u y).card) :=
    (Nat.odd_add.mp hadd).mpr (even_two_mul _)
  exact entry_centered_vanishes
    i t A R u y horbit ht hle hR hcentered hparity

end
end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
