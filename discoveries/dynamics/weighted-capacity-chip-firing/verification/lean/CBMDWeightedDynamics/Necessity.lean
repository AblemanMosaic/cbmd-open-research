import CBMDWeightedDynamics.Characterization

/-!
# Necessity of the live-set conditions

`Characterization` proves the three live-set conditions sufficient.  This module
turns the census into proof wherever it can:

* violating the **bound** on a live arc gives an explicit failing state
  (`bound_violation_defeats_transfer`);
* violating **live-closure** gives a `FilledSet`, already handled
  (`liveToDeadFilledSet`);
* the two conditions together **exclude** every `FilledSet`
  (`ordered_live_closed_excludes_filled_set`), so no obstruction of that shape
  survives them.

One direction is deliberately left out.  Turning "no rank function exists on the
live subgraph" into a concrete cycle is the classical finite-digraph fact that an
acyclic finite relation admits a topological order.  It is not specific to this
model and is not proved here; it is the sole remaining gap between the proved
statements and the exhaustive census.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDWeightedDynamics

/-- **Necessity of the bound.**  If a live `u` sends to a live `v` with
`capacity v + 1 < outdegree v + mult u v`, then loading `u` to capacity and
giving `v` exactly enough to block `u` produces a capacity-terminal state that
is not ordinarily stable.  The receiver is left below its own threshold, which
is precisely what the violated bound permits. -/
theorem bound_violation_defeats_transfer {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (positive_outdegree : ∀ w, 0 < outdegree w)
    {u v : Vertex n}
    (hu : Live outdegree capacity u)
    (arc : 0 < mult u v)
    (violated : capacity v + 1 < outdegree v + mult u v)
    (chips : Chips n)
    (at_u : chips u = capacity u)
    (at_v : chips v = capacity v + 1 - mult u v)
    (elsewhere : ∀ w, w ≠ u → w ≠ v → chips w = 0)
    (distinct : u ≠ v) :
    CapacityTerminal mult outdegree capacity chips ∧
      ¬ OrdinaryStable outdegree chips := by
  classical
  -- the receiver stays strictly below its firing threshold
  have hposv : 0 < outdegree v := positive_outdegree v
  have v_stable : chips v < outdegree v := by
    rw [at_v]; omega
  -- but it already holds enough that one more bundle overflows it
  have v_overflow : capacity v < chips v + mult u v := by
    rw [at_v]; omega
  constructor
  · intro w legal
    by_cases hw : w = v
    · subst hw
      exact (Nat.not_lt_of_ge legal.1) v_stable
    · by_cases hwu : w = u
      · subst hwu
        exact legal.2 ⟨v, arc, v_overflow⟩
      · have zero : chips w = 0 := elsewhere w hwu hw
        have unstable : outdegree w ≤ chips w := legal.1
        rw [zero] at unstable
        exact Nat.not_lt_of_ge unstable (positive_outdegree w)
  · intro stable
    have lt : chips u < outdegree u := stable u
    rw [at_u] at lt
    exact Nat.not_lt_of_ge hu lt

/-- The two structural conditions exclude every filled-set obstruction: from the
live witness the successor chain stays live, by live-closure, and strictly
raises the rank, so it cannot exist inside a finite vertex type. -/
theorem ordered_live_closed_excludes_filled_set {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (rank : Vertex n → Nat)
    (rank_lt : ∀ v, rank v < n)
    (live_ordered : ∀ u v, Live outdegree capacity u → Live outdegree capacity v →
      0 < mult u v → rank u < rank v)
    (live_closed : ∀ u v, Live outdegree capacity u → 0 < mult u v →
      Live outdegree capacity v)
    (filled : FilledSet mult outdegree capacity) : False := by
  -- no member can be both in the set and live
  have key : ∀ w : Vertex n, filled.mem w → ¬ Live outdegree capacity w := by
    intro w
    let reverseRank : Vertex n → Nat := fun z => n - rank z
    apply (measure reverseRank).wf.induction w
    intro z later memz livez
    have arc : 0 < mult z (filled.successor z) := filled.successor_arc z memz livez
    have memNext : filled.mem (filled.successor z) := filled.successor_mem z memz livez
    have liveNext : Live outdegree capacity (filled.successor z) :=
      live_closed z (filled.successor z) livez arc
    have step : rank z < rank (filled.successor z) :=
      live_ordered z (filled.successor z) livez liveNext arc
    have decreases : reverseRank (filled.successor z) < reverseRank z :=
      Nat.sub_lt_sub_left (rank_lt z) step
    exact later (filled.successor z) decreases memNext liveNext
  exact key filled.witness filled.witness_mem filled.witness_live

end CBMDWeightedDynamics
