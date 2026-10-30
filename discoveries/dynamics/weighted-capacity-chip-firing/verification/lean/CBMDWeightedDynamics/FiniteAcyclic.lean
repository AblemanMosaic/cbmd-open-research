import CBMDWeightedDynamics.Equivalence

/-!
# Finite acyclic relations are well founded

Revision 0.5.0 left one classical fact imported: that a *finite acyclic* live
subgraph is well founded.  It was no longer a step inside any theorem, only the
justification for the census deciding `WellFounded LiveArc` by cycle
detection.  This module proves it, Mathlib-free, so the decision procedure is
now justified by a compiled theorem as well.

Acyclic is stated as `∀ x, ¬ TransGen R x x`.  The measure is the number of
`R`-ancestors: if `R y x` then every ancestor of `y` is an ancestor of `x`, and
`y` is an ancestor of `x` but not of itself, so the count drops strictly.
-/

namespace CBMDWeightedDynamics

open Relation

/-- Strict growth of `countP` along a pointwise implication with one witness. -/
theorem countP_lt_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ z, p z = true → q z = true) →
      (∃ y, y ∈ l ∧ q y = true ∧ p y = false) → l.countP p < l.countP q
  | [], _, ⟨_, hy, _⟩ => absurd hy (List.not_mem_nil)
  | a :: l, imp, ⟨y, hy, hq, hp⟩ => by
    have mono : ∀ (l : List α), l.countP p ≤ l.countP q := by
      intro l
      induction l with
      | nil => simp
      | cons b l ih =>
        simp only [List.countP_cons]
        cases hb : p b
        · cases q b <;> simp <;> omega
        · simp [imp b hb]; omega
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hy with rfl | hl
    · simp [hq, hp]
      have := mono l
      omega
    · have ih := countP_lt_of_imp p q l imp ⟨y, hl, hq, hp⟩
      cases hb : p a
      · cases q a <;> simp <;> omega
      · simp [imp a hb]; omega

/-- **A finite acyclic relation is well founded.** -/
theorem wellFounded_of_acyclic {n : Nat} (R : Fin n → Fin n → Prop)
    (acyclic : ∀ x, ¬ TransGen R x x) : WellFounded R := by
  classical
  let anc : Fin n → Nat := fun x =>
    (List.finRange n).countP (fun z => decide (TransGen R z x))
  have drop : ∀ y x, R y x → anc y < anc x := by
    intro y x hyx
    apply countP_lt_of_imp
    · intro z hz
      simp only [decide_eq_true_eq] at hz ⊢
      exact TransGen.tail hz hyx
    · refine ⟨y, List.mem_finRange y, ?_, ?_⟩
      · simp only [decide_eq_true_eq]; exact TransGen.single hyx
      · simp only [decide_eq_false_iff_not]; exact acyclic y
  exact Subrelation.wf (fun {y x} h => drop y x h) (InvImage.wf anc Nat.lt_wfRel.wf)

/-- The converse: a well-founded relation has no cycle. -/
theorem acyclic_of_wellFounded {α : Type} {R : α → α → Prop} (wf : WellFounded R) :
    ∀ x, ¬ TransGen R x x := by
  intro x
  have irrefl : ∀ y, Acc (TransGen R) y → ¬ TransGen R y y := by
    intro y acc
    induction acc with
    | intro y _ ih => exact fun h => ih y h h
  exact irrefl x (wf.transGen.apply x)

/-- **Cycle detection decides the ordering hypothesis.**  On the finite vertex
type, `LiveArc` is well founded exactly when it has no cycle. -/
theorem liveArc_wellFounded_iff_acyclic {n : Nat}
    (mult : Vertex n → Vertex n → Nat) (outdegree capacity : Vertex n → Nat) :
    WellFounded (LiveArc mult outdegree capacity) ↔
      ∀ x, ¬ TransGen (LiveArc mult outdegree capacity) x x :=
  ⟨acyclic_of_wellFounded, wellFounded_of_acyclic _⟩

end CBMDWeightedDynamics
