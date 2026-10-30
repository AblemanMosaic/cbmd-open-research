import Std

/-!
# Weighted capacity-blocked chip-firing: the core obstruction

Generalizes the unit-edge obstruction of `CBMDFiniteDynamics` to arbitrary nonsink
multiplicities `mult u v`.  The capacity hypothesis is stated additively,

  `outdegree v + incomingBound v ≤ capacity v + 1`,

which is the truncation-free form of `capacity v ≥ outdegree v + incomingBound v - 1`.
Taking `incomingBound v = max_u mult u v` gives the named candidate bound; taking
`incomingBound v = 1` for unit edges recovers `capacity v ≥ outdegree v`.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDWeightedDynamics

abbrev Vertex (n : Nat) := Fin n
abbrev Chips (n : Nat) := Vertex n → Nat

def OrdinaryUnstable {n : Nat}
    (outdegree chips : Vertex n → Nat) (v : Vertex n) : Prop :=
  outdegree v ≤ chips v

def OrdinaryStable {n : Nat}
    (outdegree : Vertex n → Nat) (chips : Chips n) : Prop :=
  ∀ v, chips v < outdegree v

/-- `u` is blocked when some genuine receiver would exceed its capacity on
receiving the whole bundle `mult u v`. -/
def ReceiverBlocked {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (capacity chips : Vertex n → Nat) (u : Vertex n) : Prop :=
  ∃ v, 0 < mult u v ∧ capacity v < chips v + mult u v

def CapacityLegal {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n) (u : Vertex n) : Prop :=
  OrdinaryUnstable outdegree chips u ∧ ¬ ReceiverBlocked mult capacity chips u

def CapacityTerminal {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n) : Prop :=
  ∀ u, ¬ CapacityLegal mult outdegree capacity chips u

/-- Every arc of positive multiplicity points strictly forward. -/
def TopologicallyOrdered {n : Nat}
    (mult : Vertex n → Vertex n → Nat) : Prop :=
  ∀ ⦃u v⦄, 0 < mult u v → u.val < v.val

/-- The weighted capacity bound, in truncation-free additive form. -/
def CapacityAdmits {n : Nat}
    (outdegree capacity incomingBound : Vertex n → Nat) : Prop :=
  ∀ v, outdegree v + incomingBound v ≤ capacity v + 1

/-- **Weighted overflow lemma.**  If a receiver overflows on a bundle bounded by
`incomingBound`, and its capacity admits that bound, the receiver is ordinarily
unstable.  This is the exact point at which `incomingBound v - 1` of extra
capacity is consumed. -/
theorem weighted_overflow_forces_unstable {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity chips incomingBound : Vertex n → Nat)
    (mult_le : ∀ u v, mult u v ≤ incomingBound v)
    (admits : CapacityAdmits outdegree capacity incomingBound)
    {u v : Vertex n}
    (overflow : capacity v < chips v + mult u v) :
    OrdinaryUnstable outdegree chips v := by
  have h1 : capacity v + 1 ≤ chips v + mult u v := overflow
  have h2 : outdegree v + incomingBound v ≤ chips v + mult u v :=
    Nat.le_trans (admits v) h1
  have h3 : chips v + mult u v ≤ chips v + incomingBound v :=
    Nat.add_le_add_left (mult_le u v) _
  exact Nat.le_of_add_le_add_right (Nat.le_trans h2 h3)

/-- **Weighted preservation of terminal states.**  Under the weighted capacity
bound, a capacity-terminal state of an ordered multigraph is ordinarily stable.
The measure is reverse topological position: a blocked unstable vertex would
force a strictly later unstable receiver. -/
theorem capacity_terminal_implies_ordinary_stable {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity incomingBound : Vertex n → Nat)
    (chips : Chips n)
    (order : TopologicallyOrdered mult)
    (mult_le : ∀ u v, mult u v ≤ incomingBound v)
    (admits : CapacityAdmits outdegree capacity incomingBound)
    (terminal : CapacityTerminal mult outdegree capacity chips) :
    OrdinaryStable outdegree chips := by
  intro u
  let reverseRank : Vertex n → Nat := fun v => n - v.val
  apply (measure reverseRank).wf.induction u
  intro u later_stable
  classical
  by_cases stable : chips u < outdegree u
  · exact stable
  · exfalso
    have unstable : OrdinaryUnstable outdegree chips u := Nat.le_of_not_gt stable
    have blocked : ReceiverBlocked mult capacity chips u := by
      by_cases is_blocked : ReceiverBlocked mult capacity chips u
      · exact is_blocked
      · exact (terminal u ⟨unstable, is_blocked⟩).elim
    rcases blocked with ⟨v, hpos, overflow⟩
    have receiver_unstable : OrdinaryUnstable outdegree chips v :=
      weighted_overflow_forces_unstable mult outdegree capacity chips incomingBound
        mult_le admits overflow
    have rank_decreases : reverseRank v < reverseRank u :=
      Nat.sub_lt_sub_left u.isLt (order hpos)
    have receiver_stable : chips v < outdegree v := later_stable v rank_decreases
    exact (Nat.not_lt_of_ge receiver_unstable) receiver_stable

/-- The unit-edge hypothesis of the predecessor theorem is the case
`incomingBound = 1`. -/
theorem unit_case_capacity_admits {n : Nat}
    (outdegree capacity : Vertex n → Nat)
    (h : ∀ v, outdegree v ≤ capacity v) :
    CapacityAdmits outdegree capacity (fun _ => 1) := by
  intro v
  show outdegree v + 1 ≤ capacity v + 1
  exact Nat.succ_le_succ (h v)

end CBMDWeightedDynamics
