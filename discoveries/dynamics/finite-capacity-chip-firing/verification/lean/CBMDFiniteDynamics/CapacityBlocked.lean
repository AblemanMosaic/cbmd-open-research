import Std

/-!
# Capacity-blocked chip-firing: local obstruction lemma

This file formalizes the arithmetic step used by candidate theorem FD-C1.
It does not formalize or claim the classical ordinary chip-firing confluence
theorem.  No declaration uses `sorry`.
-/

namespace CBMDFiniteDynamics

abbrev Vertex (n : Nat) := Fin n

def OrdinaryUnstable {n : Nat}
    (outdegree chips : Vertex n → Nat) (v : Vertex n) : Prop :=
  outdegree v ≤ chips v

def ReceiverBlocked {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (capacity chips : Vertex n → Nat) (u : Vertex n) : Prop :=
  ∃ v, edge u v ∧ capacity v < chips v + 1

/-- With unit incoming transfers, overflow of an admissible receiver whose
capacity is at least its firing threshold forces that receiver to be ordinarily
unstable. -/
theorem overflow_forces_unstable {n : Nat}
    (outdegree capacity chips : Vertex n → Nat)
    (capacity_ge_outdegree : ∀ v, outdegree v ≤ capacity v)
    {v : Vertex n}
    (overflow : capacity v < chips v + 1) :
    OrdinaryUnstable outdegree chips v := by
  have hCapacityLeChips : capacity v ≤ chips v :=
    Nat.lt_succ_iff.mp overflow
  exact Nat.le_trans (capacity_ge_outdegree v) hCapacityLeChips

/-- If every receiver of `u` is ordinarily stable, then a unit transfer from
`u` cannot be blocked by receiver capacity.  In the paper proof, `u` is chosen
as a topologically latest unstable vertex of the DAG. -/
theorem not_blocked_of_receivers_stable {n : Nat}
    (edge : Vertex n → Vertex n → Prop)
    (outdegree capacity chips : Vertex n → Nat)
    (capacity_ge_outdegree : ∀ v, outdegree v ≤ capacity v)
    {u : Vertex n}
    (receivers_stable : ∀ v, edge u v → chips v < outdegree v) :
    ¬ ReceiverBlocked edge capacity chips u := by
  intro blocked
  rcases blocked with ⟨v, huv, hoverflow⟩
  have hunstable : OrdinaryUnstable outdegree chips v :=
    overflow_forces_unstable outdegree capacity chips capacity_ge_outdegree
      hoverflow
  exact (Nat.not_lt_of_ge hunstable) (receivers_stable v huv)

end CBMDFiniteDynamics
