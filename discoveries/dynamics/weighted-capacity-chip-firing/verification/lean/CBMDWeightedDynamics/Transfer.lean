import CBMDWeightedDynamics.Core

/-!
# Weighted capacity-blocked chip-firing: compiled transfer theorem

The weighted analogue of `CBMDFiniteDynamics.fd_c1_transfer`.  Ordinary firing
theory enters only as two explicit hypotheses (well-foundedness and uniqueness
of the reachable ordinarily stable state), exactly as in the unit-edge
predecessor; the capacity-specific content is `Core.capacity_terminal_implies_ordinary_stable`.

The generic reachability machinery below (`Reaches`, `Terminal`,
`wellFounded_subrelation`, `exists_reachable_terminal`) follows the predecessor
module's Mathlib-free formulation.

No declaration uses `sorry` or introduces an axiom beyond Lean's standard three.
-/

namespace CBMDWeightedDynamics

def OrdinaryStep {n : Nat}
    (fire : Chips n → Vertex n → Chips n)
    (outdegree : Vertex n → Nat)
    (before after : Chips n) : Prop :=
  ∃ u, OrdinaryUnstable outdegree before u ∧ fire before u = after

def CapacityStep {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    (before after : Chips n) : Prop :=
  ∃ u, CapacityLegal mult outdegree capacity before u ∧ fire before u = after

theorem capacity_step_is_ordinary_step {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    {before after : Chips n}
    (step : CapacityStep mult fire outdegree capacity before after) :
    OrdinaryStep fire outdegree before after := by
  rcases step with ⟨u, legal, fired⟩
  exact ⟨u, legal.1, fired⟩

inductive Reaches {α : Sort _} (step : α → α → Prop) : α → α → Prop
  | refl (x : α) : Reaches step x x
  | tail {x y z : α} : Reaches step x y → step y z → Reaches step x z

namespace Reaches

theorem head {α : Sort _} {step : α → α → Prop} {x y z : α}
    (first : step x y) (rest : Reaches step y z) : Reaches step x z := by
  induction rest with
  | refl => exact Reaches.tail (Reaches.refl x) first
  | tail path last ih => exact Reaches.tail ih last

theorem mono {α : Sort _} {smaller larger : α → α → Prop}
    (included : ∀ ⦃x y⦄, smaller x y → larger x y)
    {x y : α} (path : Reaches smaller x y) : Reaches larger x y := by
  induction path with
  | refl => exact Reaches.refl x
  | tail path last ih => exact Reaches.tail ih (included last)

end Reaches

def Terminal {α : Sort _} (step : α → α → Prop) (x : α) : Prop :=
  ∀ y, ¬ step x y

theorem wellFounded_subrelation {α : Sort _}
    {larger smaller : α → α → Prop}
    (larger_wf : WellFounded (fun y x => larger x y))
    (included : ∀ ⦃x y⦄, smaller x y → larger x y) :
    WellFounded (fun y x => smaller x y) :=
  Subrelation.wf (fun step => included step) larger_wf

theorem terminal_capacity_step_implies_capacity_terminal {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n)
    (terminal : Terminal (CapacityStep mult fire outdegree capacity) chips) :
    CapacityTerminal mult outdegree capacity chips := by
  intro u legal
  exact terminal (fire chips u) ⟨u, legal, rfl⟩

theorem exists_reachable_terminal {α : Sort _}
    (step : α → α → Prop)
    (step_wf : WellFounded (fun y x => step x y))
    (initial : α) :
    ∃ final, Reaches step initial final ∧ Terminal step final := by
  classical
  apply step_wf.induction initial
  intro state normalize_later
  by_cases has_next : ∃ next, step state next
  · rcases has_next with ⟨next, one_step⟩
    rcases normalize_later next one_step with ⟨final, path, terminal⟩
    exact ⟨final, Reaches.head one_step path, terminal⟩
  · exact ⟨state, Reaches.refl state, fun next step => has_next ⟨next, step⟩⟩

theorem every_capacity_terminal_eq_ordinary_normal {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity incomingBound : Vertex n → Nat)
    (initial ordinaryNormal final : Chips n)
    (order : TopologicallyOrdered mult)
    (mult_le : ∀ u v, mult u v ≤ incomingBound v)
    (admits : CapacityAdmits outdegree capacity incomingBound)
    (capacity_path :
      Reaches (CapacityStep mult fire outdegree capacity) initial final)
    (capacity_terminal : CapacityTerminal mult outdegree capacity final)
    (ordinary_unique : ∀ state,
      Reaches (OrdinaryStep fire outdegree) initial state →
      OrdinaryStable outdegree state → state = ordinaryNormal) :
    final = ordinaryNormal := by
  have ordinary_path : Reaches (OrdinaryStep fire outdegree) initial final :=
    Reaches.mono
      (fun {before after} step =>
        capacity_step_is_ordinary_step mult fire outdegree capacity
          (before := before) (after := after) step)
      capacity_path
  have ordinary_stable : OrdinaryStable outdegree final :=
    capacity_terminal_implies_ordinary_stable mult outdegree capacity incomingBound
      final order mult_le admits capacity_terminal
  exact ordinary_unique final ordinary_path ordinary_stable

/-- **Weighted transfer theorem.**  For an ordered multigraph whose capacities
satisfy `outdegree v + incomingBound v ≤ capacity v + 1`, if ordinary firing is
well-founded with a unique reachable stable state, then capacity-blocked
weighted firing terminates and every capacity-terminal result is that same
ordinary normal form. -/
theorem weighted_transfer {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity incomingBound : Vertex n → Nat)
    (initial ordinaryNormal : Chips n)
    (order : TopologicallyOrdered mult)
    (mult_le : ∀ u v, mult u v ≤ incomingBound v)
    (admits : CapacityAdmits outdegree capacity incomingBound)
    (ordinary_wf :
      WellFounded (fun after before => OrdinaryStep fire outdegree before after))
    (ordinary_unique : ∀ state,
      Reaches (OrdinaryStep fire outdegree) initial state →
      OrdinaryStable outdegree state → state = ordinaryNormal) :
    (∃ final,
      Reaches (CapacityStep mult fire outdegree capacity) initial final ∧
      CapacityTerminal mult outdegree capacity final ∧
      final = ordinaryNormal) ∧
    (∀ final,
      Reaches (CapacityStep mult fire outdegree capacity) initial final →
      CapacityTerminal mult outdegree capacity final →
      final = ordinaryNormal) := by
  have capacity_wf :
      WellFounded (fun after before =>
        CapacityStep mult fire outdegree capacity before after) :=
    wellFounded_subrelation ordinary_wf
      (fun {before after} step =>
        capacity_step_is_ordinary_step mult fire outdegree capacity
          (before := before) (after := after) step)
  rcases exists_reachable_terminal
      (CapacityStep mult fire outdegree capacity) capacity_wf initial with
    ⟨final, path, relation_terminal⟩
  have terminal : CapacityTerminal mult outdegree capacity final :=
    terminal_capacity_step_implies_capacity_terminal
      mult fire outdegree capacity final relation_terminal
  have final_eq : final = ordinaryNormal :=
    every_capacity_terminal_eq_ordinary_normal
      mult fire outdegree capacity incomingBound initial ordinaryNormal final
      order mult_le admits path terminal ordinary_unique
  refine ⟨⟨final, path, terminal, final_eq⟩, ?_⟩
  intro other other_path other_terminal
  exact every_capacity_terminal_eq_ordinary_normal
    mult fire outdegree capacity incomingBound initial ordinaryNormal other
    order mult_le admits other_path other_terminal ordinary_unique

end CBMDWeightedDynamics
