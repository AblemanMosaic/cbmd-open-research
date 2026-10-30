import CBMDOwnerFiber.Core

/-!
# From amplitude support to row support

`support_in_orbit` is a hypothesis of the compiled theorems.  For the source
row it splits into two facts: the row is the indicator at `y = u` plus a term
that is a multiple of the integer amplitude, and the amplitude vanishes off the
orbit.  The second is compiled natively (`entry_eq_zero_of_not_inOrbit` in
`proofs/native`).  This module compiles the first step: those two facts give
`support_in_orbit` for the row, whatever the row's coefficient ring.
-/

namespace CBMDOwnerFiber

variable {Q r : Nat}

/-- The row step.  If the row vanishes off the diagonal wherever the amplitude
vanishes, and the amplitude vanishes off the orbit, the row is supported in the
orbit. -/
theorem row_support_in_orbit {β γ : Type} [Zero β] [Zero γ]
    (row : Typ Q r → Typ Q r → β) (amp : Typ Q r → Typ Q r → γ)
    (row_form : ∀ u y, y ≠ u → amp u y = 0 → row u y = 0)
    (amp_support : ∀ u y, amp u y ≠ 0 → InOrbit u y) :
    ∀ u y, row u y ≠ 0 → InOrbit u y := by
  intro u y hrow
  by_cases e : y = u
  · subst e; exact inOrbit_refl y
  · by_cases ha : amp u y = 0
    · exact absurd (row_form u y e ha) hrow
    · exact amp_support u y ha

end CBMDOwnerFiber
