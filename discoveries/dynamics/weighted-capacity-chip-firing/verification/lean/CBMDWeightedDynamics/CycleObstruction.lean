import CBMDWeightedDynamics.Core

/-!
# The ordered hypothesis cannot be removed, and no capacity replaces it

`Core` and `Transfer` prove preservation for forward-ordered multigraphs.  This
module shows the ordering is not a technical convenience: as soon as the arc
relation carries a directed cycle, preservation fails at **every** capacity
meeting the natural threshold `outdegree v ≤ capacity v`.  Enlarging capacity
never helps, because the counterexample is built from the capacities themselves.

A directed cycle is presented here as a nonempty vertex set closed under a
successor map along positive-multiplicity arcs.  On a finite vertex type such a
set exists exactly when the arc relation has a directed cycle, and
`ordered_has_no_closed_set` shows a forward ordering excludes it.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDWeightedDynamics

/-- A nonempty set closed under a successor map along positive arcs. -/
structure ClosedCycle {n : Nat} (mult : Vertex n → Vertex n → Nat) where
  onCycle : Vertex n → Prop
  next : Vertex n → Vertex n
  closed : ∀ v, onCycle v → onCycle (next v)
  arc : ∀ v, onCycle v → 0 < mult v (next v)
  witness : Vertex n
  witness_mem : onCycle witness

/-- A forward-ordered arc relation admits no such set: the successor map would
raise the index forever inside a finite type. -/
theorem ordered_has_no_closed_set {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (order : TopologicallyOrdered mult)
    (cycle : ClosedCycle mult) : False := by
  have key : ∀ v : Vertex n, ¬ cycle.onCycle v := by
    intro v
    let reverseRank : Vertex n → Nat := fun w => n - w.val
    apply (measure reverseRank).wf.induction v
    intro w later mem
    have memNext : cycle.onCycle (cycle.next w) := cycle.closed w mem
    have step : w.val < (cycle.next w).val := order (cycle.arc w mem)
    have rank : reverseRank (cycle.next w) < reverseRank w :=
      Nat.sub_lt_sub_left w.isLt step
    exact later (cycle.next w) rank memNext
  exact key cycle.witness cycle.witness_mem

/-- **Cycle obstruction.**  Fill every cycle vertex to its capacity and empty
every other vertex.  Every cycle vertex is blocked by its successor, every other
vertex is ordinarily stable, so the state is capacity-terminal; yet the cycle
vertices hold at least their own thresholds, so it is not ordinarily stable.
The hypothesis `outdegree v ≤ capacity v` is the weakest natural threshold, and
the conclusion is independent of how large the capacities are. -/
theorem cycle_defeats_every_capacity {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (cycle : ClosedCycle mult)
    (capacity_ge : ∀ v, cycle.onCycle v → outdegree v ≤ capacity v)
    (positive_outdegree : ∀ u, 0 < outdegree u)
    (chips : Chips n)
    (full : ∀ v, cycle.onCycle v → chips v = capacity v)
    (empty : ∀ v, ¬ cycle.onCycle v → chips v = 0) :
    CapacityTerminal mult outdegree capacity chips ∧
      ¬ OrdinaryStable outdegree chips := by
  constructor
  · intro u legal
    classical
    by_cases mem : cycle.onCycle u
    · -- blocked by the successor, which is itself full
      have arc : 0 < mult u (cycle.next u) := cycle.arc u mem
      have memNext : cycle.onCycle (cycle.next u) := cycle.closed u mem
      have fullNext : chips (cycle.next u) = capacity (cycle.next u) := full _ memNext
      have overflow :
          capacity (cycle.next u) < chips (cycle.next u) + mult u (cycle.next u) := by
        rw [fullNext]
        exact Nat.lt_add_of_pos_right arc
      exact legal.2 ⟨cycle.next u, arc, overflow⟩
    · -- empty, hence ordinarily stable, hence not legal
      have zero : chips u = 0 := empty u mem
      have unstable : outdegree u ≤ chips u := legal.1
      rw [zero] at unstable
      exact Nat.not_lt_of_ge unstable (positive_outdegree u)
  · intro stable
    have mem := cycle.witness_mem
    have fullW : chips cycle.witness = capacity cycle.witness := full _ mem
    have ge : outdegree cycle.witness ≤ capacity cycle.witness := capacity_ge _ mem
    have lt : chips cycle.witness < outdegree cycle.witness := stable cycle.witness
    rw [fullW] at lt
    exact Nat.not_lt_of_ge ge lt

end CBMDWeightedDynamics
