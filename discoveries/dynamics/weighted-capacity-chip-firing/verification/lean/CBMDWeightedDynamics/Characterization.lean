import CBMDWeightedDynamics.Core

/-!
# Characterization over arbitrary digraphs and arbitrary capacities

`Core` assumes every arc points forward and every vertex is able to fire.  Over
arbitrary digraphs with arbitrary capacities the right notion is the **live** set

  `Live v  ↔  outdegree v ≤ capacity v`,

the vertices that can ever hold enough chips to fire.  A vertex outside it is
permanently ordinarily stable, because its chip count never exceeds its capacity.

Three conditions on the live set turn out to be jointly sufficient, and an
exhaustive census shows each is separately necessary:

1. the arcs among live vertices are ordered by a rank (acyclicity),
2. `outdegree v + mult u v ≤ capacity v + 1` for live `u → v`,
3. live vertices send only to live vertices.

`live_terminal_implies_ordinary_stable` proves sufficiency.
`filled_set_obstruction` is a single obstruction that yields the failure of 1
and of 3 as corollaries: both the cycle and the live-to-dead case are a set held
full by members that can never drain.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDWeightedDynamics

/-- A vertex that can ever reach its own firing threshold inside the capacity box. -/
def Live {n : Nat} (outdegree capacity : Vertex n → Nat) (v : Vertex n) : Prop :=
  outdegree v ≤ capacity v

/-- A vertex outside the live set is ordinarily stable at every admissible state. -/
theorem dead_is_ordinarily_stable {n : Nat}
    (outdegree capacity : Vertex n → Nat) (chips : Chips n)
    (admissible : ∀ v, chips v ≤ capacity v)
    {v : Vertex n} (dead : ¬ Live outdegree capacity v) :
    chips v < outdegree v :=
  Nat.lt_of_le_of_lt (admissible v) (Nat.lt_of_not_le dead)

/-- **Sufficiency.**  Under the three live-set conditions, a capacity-terminal
admissible state is ordinarily stable.  Dead vertices are stable outright; live
vertices descend along the rank of the live subgraph. -/
theorem live_terminal_implies_ordinary_stable {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (rank : Vertex n → Nat)
    (chips : Chips n)
    (admissible : ∀ v, chips v ≤ capacity v)
    (rank_lt : ∀ v, rank v < n)
    (live_ordered : ∀ u v, Live outdegree capacity u → Live outdegree capacity v →
      0 < mult u v → rank u < rank v)
    (live_closed : ∀ u v, Live outdegree capacity u → 0 < mult u v →
      Live outdegree capacity v)
    (live_bound : ∀ u v, Live outdegree capacity u → Live outdegree capacity v →
      0 < mult u v → outdegree v + mult u v ≤ capacity v + 1)
    (terminal : CapacityTerminal mult outdegree capacity chips) :
    OrdinaryStable outdegree chips := by
  classical
  intro u
  by_cases hu : Live outdegree capacity u
  · -- live: well-founded descent on reverse rank inside the live subgraph
    revert hu
    let reverseRank : Vertex n → Nat := fun w => n - rank w
    apply (measure reverseRank).wf.induction u
    intro w later hw
    by_cases stable : chips w < outdegree w
    · exact stable
    · exfalso
      have unstable : OrdinaryUnstable outdegree chips w := Nat.le_of_not_gt stable
      have blocked : ReceiverBlocked mult capacity chips w := by
        by_cases b : ReceiverBlocked mult capacity chips w
        · exact b
        · exact (terminal w ⟨unstable, b⟩).elim
      rcases blocked with ⟨v, hpos, overflow⟩
      have hv : Live outdegree capacity v := live_closed w v hw hpos
      -- the bound turns overflow into instability of the receiver
      have h1 : capacity v + 1 ≤ chips v + mult w v := overflow
      have h2 : outdegree v + mult w v ≤ chips v + mult w v :=
        Nat.le_trans (live_bound w v hw hv hpos) h1
      have receiver_unstable : outdegree v ≤ chips v :=
        Nat.le_of_add_le_add_right h2
      have rank_decreases : reverseRank v < reverseRank w :=
        Nat.sub_lt_sub_left (rank_lt w) (live_ordered w v hw hv hpos)
      exact (Nat.not_lt_of_ge receiver_unstable) (later v rank_decreases hv)
  · exact dead_is_ordinarily_stable outdegree capacity chips admissible hu

/-- A set held full, whose live members all point back into it. -/
structure FilledSet {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat) where
  mem : Vertex n → Prop
  /-- every live member has a positive arc to another member -/
  successor : Vertex n → Vertex n
  successor_mem : ∀ v, mem v → Live outdegree capacity v → mem (successor v)
  successor_arc : ∀ v, mem v → Live outdegree capacity v → 0 < mult v (successor v)
  witness : Vertex n
  witness_mem : mem witness
  witness_live : Live outdegree capacity witness

/-- **Obstruction.**  Fill the set, empty everything else: the state is
capacity-terminal yet not ordinarily stable.  Live members are blocked by their
full successors, dead members are below their own thresholds, and non-members
are empty.  The construction uses the capacities themselves, so no enlargement
of capacity escapes it.

A directed cycle among live vertices and a live vertex pointing at a dead one
are both instances: in the first the successor is the next cycle vertex, in the
second the live vertex points at the dead one and the dead one needs no
successor. -/
theorem filled_set_obstruction {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (filled : FilledSet mult outdegree capacity)
    (positive_outdegree : ∀ u, 0 < outdegree u)
    (chips : Chips n)
    (full : ∀ v, filled.mem v → chips v = capacity v)
    (empty : ∀ v, ¬ filled.mem v → chips v = 0) :
    CapacityTerminal mult outdegree capacity chips ∧
      ¬ OrdinaryStable outdegree chips := by
  classical
  constructor
  · intro u legal
    by_cases mem : filled.mem u
    · by_cases hlive : Live outdegree capacity u
      · -- blocked by a full successor
        have arc : 0 < mult u (filled.successor u) := filled.successor_arc u mem hlive
        have memNext : filled.mem (filled.successor u) := filled.successor_mem u mem hlive
        have fullNext : chips (filled.successor u) = capacity (filled.successor u) :=
          full _ memNext
        have overflow : capacity (filled.successor u) <
            chips (filled.successor u) + mult u (filled.successor u) := by
          rw [fullNext]; exact Nat.lt_add_of_pos_right arc
        exact legal.2 ⟨filled.successor u, arc, overflow⟩
      · -- dead: its chips equal its capacity, which is below its threshold
        have hfull : chips u = capacity u := full u mem
        have unstable : outdegree u ≤ chips u := legal.1
        rw [hfull] at unstable
        exact hlive unstable
    · -- empty, hence stable
      have zero : chips u = 0 := empty u mem
      have unstable : outdegree u ≤ chips u := legal.1
      rw [zero] at unstable
      exact Nat.not_lt_of_ge unstable (positive_outdegree u)
  · intro stable
    have hfull : chips filled.witness = capacity filled.witness := full _ filled.witness_mem
    have lt : chips filled.witness < outdegree filled.witness := stable filled.witness
    rw [hfull] at lt
    exact Nat.not_lt_of_ge filled.witness_live lt

/-- A live vertex with an arc to a dead vertex is a filled set on two members. -/
def liveToDeadFilledSet {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    {u v : Vertex n}
    (hu : Live outdegree capacity u)
    (hv : ¬ Live outdegree capacity v)
    (arc : 0 < mult u v) :
    FilledSet mult outdegree capacity where
  mem w := w = u ∨ w = v
  successor _ := v
  successor_mem _ _ _ := Or.inr rfl
  successor_arc w hw hlive := by
    rcases hw with rfl | rfl
    · exact arc
    · exact absurd hlive hv
  witness := u
  witness_mem := Or.inl rfl
  witness_live := hu

end CBMDWeightedDynamics
