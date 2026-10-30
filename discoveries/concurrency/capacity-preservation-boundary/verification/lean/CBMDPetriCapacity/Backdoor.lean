import CBMDPetriCapacity.Core

/-!
# Few multi-input transitions: the max-closure survives branching

Revision 0.4.0 shows preservation is coNP-complete once transitions may have
two input places.  The hardness uses unboundedly many of them.  This module is
the lemma behind a fixed-parameter algorithm in their number `k`.

A single-input transition `t`, consuming only at `s`, is a dual-Horn clause:
the set of markings at which it is not capacity-enabled is closed under
pointwise maximum (`notCapEnabled_max_of_single`, the per-transition form of
`SNet.capDead_max`).  A multi-input transition is blocked exactly when one of
finitely many unit conditions holds — an input below its demand (an upper
bound) or some place overflowing (a lower bound) — and unit bounds are closed
under maximum too (`ub_max`, `lb_max`).

So once a blocking condition has been **chosen** for each multi-input
transition, the remaining constraint set is max-closed, a greatest admissible
solution exists, and because lower bounds and ordinary enabledness are
upward-closed, that one marking decides the branch.  Branching costs at most
`(2P)^k`.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDPetriCapacity

variable {P T : Nat}

/-- `t` consumes only at `s`. -/
def SingleAt (N : Net P T) (t : Fin T) (s : Fin P) : Prop :=
  ∀ q, q ≠ s → N.pre t q = 0

/-- **The per-transition closure.**  If a single-input transition is not
capacity-enabled at two admissible markings, it is not capacity-enabled at
their maximum. -/
theorem notCapEnabled_max_of_single {N : Net P T} {cap m₁ m₂ : Marking P}
    {t : Fin T} {s : Fin P} (single : SingleAt N t s)
    (d₁ : ¬ CapEnabled N cap m₁ t) (d₂ : ¬ CapEnabled N cap m₂ t) :
    ¬ CapEnabled N cap (fun q => Nat.max (m₁ q) (m₂ q)) t := by
  intro ⟨en, fits⟩
  have main : ∀ mi : Marking P,
      (∀ q, mi q ≤ Nat.max (m₁ q) (m₂ q)) →
      Nat.max (m₁ s) (m₂ s) ≤ mi s → CapEnabled N cap mi t := by
    intro mi hle hat
    refine ⟨fun q => ?_, fun q => ?_⟩
    · by_cases hq : q = s
      · subst hq; exact Nat.le_trans (en q) hat
      · rw [single q hq]; exact Nat.zero_le _
    · have hf : Nat.max (m₁ q) (m₂ q) - N.pre t q + N.post t q ≤ cap q := fits q
      have hm := hle q
      by_cases hq : q = s
      · subst hq
        have : mi q = Nat.max (m₁ q) (m₂ q) := Nat.le_antisymm hm hat
        omega
      · rw [single q hq] at hf ⊢; omega
  rcases Nat.le_total (m₂ s) (m₁ s) with h | h
  · exact d₁ (main m₁ (fun q => Nat.le_max_left _ _) (Nat.max_le.mpr ⟨Nat.le_refl _, h⟩))
  · exact d₂ (main m₂ (fun q => Nat.le_max_right _ _) (Nat.max_le.mpr ⟨h, Nat.le_refl _⟩))

/-- Upper bounds are closed under maximum. -/
theorem ub_max {m₁ m₂ : Marking P} {q : Fin P} {b : Nat}
    (h₁ : m₁ q ≤ b) (h₂ : m₂ q ≤ b) : Nat.max (m₁ q) (m₂ q) ≤ b :=
  Nat.max_le.mpr ⟨h₁, h₂⟩

/-- Lower bounds are closed under maximum. -/
theorem lb_max {m₁ m₂ : Marking P} {q : Fin P} {b : Nat}
    (h₁ : b ≤ m₁ q) : b ≤ Nat.max (m₁ q) (m₂ q) :=
  Nat.le_trans h₁ (Nat.le_max_left _ _)

/-- A chosen lower bound at an overflowing place really does block `t`:
if `m q ≥ cap q - post t q + pre t q + 1` then firing `t` overflows `q`. -/
theorem lower_bound_blocks {N : Net P T} {cap m : Marking P} {t : Fin T} {q : Fin P}
    (hq : cap q + N.pre t q < m q + N.post t q) :
    ¬ CapEnabled N cap m t := by
  intro ⟨en, fits⟩
  have := fits q
  have := en q
  omega

/-- A chosen upper bound at an input really does block `t`. -/
theorem upper_bound_blocks {N : Net P T} {m cap : Marking P} {t : Fin T} {q : Fin P}
    (hq : m q < N.pre t q) : ¬ CapEnabled N cap m t :=
  fun ⟨en, _⟩ => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hq (en q))

/-- **The branching is exhaustive.**  A transition that is not capacity-enabled
is blocked by one of the enumerated unit literals: some input below its demand,
or some place overflowing.  Without this, a bad marking could fall between the
branches. -/
theorem blocked_by_some_literal {N : Net P T} {cap m : Marking P} {t : Fin T}
    (h : ¬ CapEnabled N cap m t) :
    (∃ q, m q < N.pre t q) ∨ (∃ q, cap q + N.pre t q < m q + N.post t q) := by
  classical
  by_cases hin : ∃ q, m q < N.pre t q
  · exact Or.inl hin
  · refine Or.inr (Classical.byContradiction (fun hno => h ⟨fun q => ?_, fun q => ?_⟩))
    · exact Nat.le_of_not_lt (fun hlt => hin ⟨q, hlt⟩)
    · have hle : N.pre t q ≤ m q := Nat.le_of_not_lt (fun hlt => hin ⟨q, hlt⟩)
      have hnot : ¬ cap q + N.pre t q < m q + N.post t q := fun hh => hno ⟨q, hh⟩
      omega

end CBMDPetriCapacity
