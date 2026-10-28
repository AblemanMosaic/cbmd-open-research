import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixSupport

/-!
# Orbit facts for the entry closed-form bridge

This file isolates source-correspondence facts that do not depend on the
admitted centered-vanishing workbench.  It is intended to be compiled and
escape-scanned as its own proof boundary.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- Positions at which the head and selected slot of a target differ. -/
def activeSet (i : Fin Δ) (u : UniversalType r Q Δ) : Finset (Fin Q) :=
  Finset.univ.filter (fun l => u.head l ≠ u.slot i l)

/-- Membership in the selected-slot swap orbit. -/
def InOrbit (i : Fin Δ) (u y : UniversalType r Q Δ) : Prop :=
  ∃ s : Finset (Fin Q), y = swapPositions i s u

/-- Along a swap orbit, mismatches are exactly the active coordinates not
selected by the witnessing swap set. -/
@[simp] theorem mismatches_swapPositions (i : Fin Δ) (s : Finset (Fin Q))
    (u : UniversalType r Q Δ) :
    mismatches i u (swapPositions i s u) = activeSet i u \ s := by
  ext l
  by_cases hls : l ∈ s <;> simp [mismatches, activeSet, hls]

/-- No mismatch can occur outside the coordinates on which a swap changes the
state. -/
theorem mismatches_subset_activeSet_of_inOrbit (i : Fin Δ)
    (u y : UniversalType r Q Δ) (horbit : InOrbit i u y) :
    mismatches i u y ⊆ activeSet i u := by
  obtain ⟨s, rfl⟩ := horbit
  simp

/-- Two swap sets produce the same state exactly when they agree on the
coordinates where the head and selected slot are distinct. -/
theorem swapPositions_eq_iff_inter_activeSet (i : Fin Δ)
    (a b : Finset (Fin Q)) (u : UniversalType r Q Δ) :
    swapPositions i a u = swapPositions i b u ↔
      a ∩ activeSet i u = b ∩ activeSet i u := by
  constructor
  · intro h
    ext l
    simp only [Finset.mem_inter]
    constructor
    · rintro ⟨hla, hlactive⟩
      refine ⟨?_, hlactive⟩
      by_contra hlb
      have hhead := congrArg (fun v => v.head l) h
      have hne : u.head l ≠ u.slot i l := by
        simpa [activeSet] using hlactive
      simp [hla, hlb] at hhead
      exact hne hhead.symm
    · rintro ⟨hlb, hlactive⟩
      refine ⟨?_, hlactive⟩
      by_contra hla
      have hhead := congrArg (fun v => v.head l) h
      have hne : u.head l ≠ u.slot i l := by
        simpa [activeSet] using hlactive
      simp [hla, hlb] at hhead
      exact hne hhead
  · intro hinter
    apply UniversalType.ext
    · funext l
      by_cases hlactive : l ∈ activeSet i u
      · have hmem : l ∈ a ↔ l ∈ b := by
          have h := Finset.ext_iff.mp hinter l
          simpa [hlactive] using h
        by_cases hla : l ∈ a <;> simp_all
      · have heq : u.head l = u.slot i l := by
          simpa [activeSet] using hlactive
        by_cases hla : l ∈ a <;> simp [hla, heq]
    · funext j l
      by_cases hji : j = i
      · subst j
        by_cases hlactive : l ∈ activeSet i u
        · have hmem : l ∈ a ↔ l ∈ b := by
            have h := Finset.ext_iff.mp hinter l
            simpa [hlactive] using h
          by_cases hla : l ∈ a <;> simp_all
        · have heq : u.head l = u.slot i l := by
            simpa [activeSet] using hlactive
          by_cases hla : l ∈ a <;> simp [hla, heq]
      · simp [swapPositions_slot_other, hji]

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
