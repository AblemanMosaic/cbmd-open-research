import CBMDFiniteDynamics.CapacityBlocked

/-!
# Capacity-blocked chip-firing: compiled transfer theorem

This file formalizes the complete structural transfer argument behind FD-C1.
The ordinary chip-firing result is exposed as two explicit hypotheses:
well-foundedness and uniqueness of the reachable ordinarily stable state.  The
capacity and ordinary relations use the same firing function.  No declaration
uses `sorry` or introduces an axiom.
-/

namespace CBMDFiniteDynamics

abbrev Chips (n : Nat) := Vertex n → Nat

def OrdinaryStable {n : Nat}
    (outdegree : Vertex n → Nat) (chips : Chips n) : Prop :=
  ∀ v, chips v < outdegree v

def CapacityLegal {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n) (u : Vertex n) : Prop :=
  OrdinaryUnstable outdegree chips u ∧
    ¬ ReceiverBlocked edge capacity chips u

def CapacityTerminal {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n) : Prop :=
  ∀ u, ¬ CapacityLegal edge outdegree capacity chips u

/-- Edges point strictly forward in the chosen finite topological order. -/
def TopologicallyOrdered {n : Nat}
    (edge : Vertex n → Vertex n → Prop) : Prop :=
  ∀ ⦃u v⦄, edge u v → u.val < v.val

/-- A capacity-terminal state in the ordered unit-edge class is ordinarily
stable.  The well-founded measure is reverse topological position, so a
blocked unstable vertex would have a later unstable receiver. -/
theorem capacity_terminal_implies_ordinary_stable {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n)
    (edge_order : TopologicallyOrdered edge)
    (capacity_ge_outdegree : ∀ v, outdegree v ≤ capacity v)
    (terminal : CapacityTerminal edge outdegree capacity chips) :
    OrdinaryStable outdegree chips := by
  intro u
  let reverseRank : Vertex n → Nat := fun v => n - v.val
  apply (measure reverseRank).wf.induction u
  intro u later_stable
  classical
  by_cases stable : chips u < outdegree u
  · exact stable
  · exfalso
    have unstable : OrdinaryUnstable outdegree chips u :=
      Nat.le_of_not_gt stable
    have blocked : ReceiverBlocked edge capacity chips u := by
      by_cases is_blocked : ReceiverBlocked edge capacity chips u
      · exact is_blocked
      · exact (terminal u ⟨unstable, is_blocked⟩).elim
    rcases blocked with ⟨v, huv, overflow⟩
    have receiver_unstable : OrdinaryUnstable outdegree chips v :=
      overflow_forces_unstable outdegree capacity chips
        capacity_ge_outdegree overflow
    have rank_decreases : reverseRank v < reverseRank u :=
      Nat.sub_lt_sub_left u.isLt (edge_order huv)
    have receiver_stable : chips v < outdegree v :=
      later_stable v rank_decreases
    exact (Nat.not_lt_of_ge receiver_unstable) receiver_stable

def OrdinaryStep {n : Nat}
    (fire : Chips n → Vertex n → Chips n)
    (outdegree : Vertex n → Nat)
    (before after : Chips n) : Prop :=
  ∃ u, OrdinaryUnstable outdegree before u ∧ fire before u = after

def CapacityStep {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    (before after : Chips n) : Prop :=
  ∃ u, CapacityLegal edge outdegree capacity before u ∧
    fire before u = after

theorem capacity_step_is_ordinary_step {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    {before after : Chips n}
    (step : CapacityStep edge fire outdegree capacity before after) :
    OrdinaryStep fire outdegree before after := by
  rcases step with ⟨u, legal, fired⟩
  exact ⟨u, legal.1, fired⟩

/-- Reflexive transitive closure, kept local so the module has no Mathlib
dependency. -/
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
    WellFounded (fun y x => smaller x y) := by
  exact Subrelation.wf (fun step => included step) larger_wf

theorem terminal_capacity_step_implies_capacity_terminal {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n)
    (terminal :
      Terminal (CapacityStep edge fire outdegree capacity) chips) :
    CapacityTerminal edge outdegree capacity chips := by
  intro u legal
  exact terminal (fire chips u) ⟨u, legal, rfl⟩

/-- Every state of a well-founded forward relation reaches a terminal state. -/
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

/-- Any reachable capacity-terminal state equals the ordinary normal form when
ordinary stabilization is unique. -/
theorem every_capacity_terminal_eq_ordinary_normal {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    (initial ordinaryNormal final : Chips n)
    (edge_order : TopologicallyOrdered edge)
    (capacity_ge_outdegree : ∀ v, outdegree v ≤ capacity v)
    (capacity_path :
      Reaches (CapacityStep edge fire outdegree capacity) initial final)
    (capacity_terminal : CapacityTerminal edge outdegree capacity final)
    (ordinary_unique : ∀ state,
      Reaches (OrdinaryStep fire outdegree) initial state →
      OrdinaryStable outdegree state → state = ordinaryNormal) :
    final = ordinaryNormal := by
  have ordinary_path :
      Reaches (OrdinaryStep fire outdegree) initial final :=
    Reaches.mono
      (fun {before after} step =>
        capacity_step_is_ordinary_step edge fire outdegree capacity
          (before := before) (after := after) step)
      capacity_path
  have ordinary_stable : OrdinaryStable outdegree final :=
    capacity_terminal_implies_ordinary_stable edge outdegree capacity final
      edge_order capacity_ge_outdegree capacity_terminal
  exact ordinary_unique final ordinary_path ordinary_stable

/-- Compiled FD-C1 transfer theorem.  If ordinary firing is well-founded and
has a unique reachable stable state, then capacity-blocked firing terminates,
and every capacity-terminal result is that same ordinary normal form. -/
theorem fd_c1_transfer {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    (initial ordinaryNormal : Chips n)
    (edge_order : TopologicallyOrdered edge)
    (capacity_ge_outdegree : ∀ v, outdegree v ≤ capacity v)
    (ordinary_wf :
      WellFounded (fun after before =>
        OrdinaryStep fire outdegree before after))
    (ordinary_unique : ∀ state,
      Reaches (OrdinaryStep fire outdegree) initial state →
      OrdinaryStable outdegree state → state = ordinaryNormal) :
    (∃ final,
      Reaches (CapacityStep edge fire outdegree capacity) initial final ∧
      CapacityTerminal edge outdegree capacity final ∧
      final = ordinaryNormal) ∧
    (∀ final,
      Reaches (CapacityStep edge fire outdegree capacity) initial final →
      CapacityTerminal edge outdegree capacity final →
      final = ordinaryNormal) := by
  have capacity_wf :
      WellFounded (fun after before =>
        CapacityStep edge fire outdegree capacity before after) :=
    wellFounded_subrelation ordinary_wf
      (fun {before after} step =>
        capacity_step_is_ordinary_step edge fire outdegree capacity
          (before := before) (after := after) step)
  rcases exists_reachable_terminal
      (CapacityStep edge fire outdegree capacity) capacity_wf initial with
    ⟨final, path, relation_terminal⟩
  have terminal : CapacityTerminal edge outdegree capacity final :=
    terminal_capacity_step_implies_capacity_terminal
      edge fire outdegree capacity final relation_terminal
  have final_eq : final = ordinaryNormal :=
    every_capacity_terminal_eq_ordinary_normal
      edge fire outdegree capacity initial ordinaryNormal final
      edge_order capacity_ge_outdegree path terminal ordinary_unique
  constructor
  · exact ⟨final, path, terminal, final_eq⟩
  · intro other other_path other_terminal
    exact every_capacity_terminal_eq_ordinary_normal
      edge fire outdegree capacity initial ordinaryNormal other
      edge_order capacity_ge_outdegree other_path other_terminal
      ordinary_unique

end CBMDFiniteDynamics
