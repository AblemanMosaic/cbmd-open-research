import CBMDWeightedDynamics.Necessity
import CBMDWeightedDynamics.CycleObstruction

/-!
# Closing the gap: a proved equivalence

`Characterization` and `Necessity` left one step unproved — turning "no rank
function exists on the live subgraph" into a concrete obstruction.  That step was
the classical finite-digraph fact that an acyclic finite relation admits a
topological order, imported as the hypotheses `rank` / `rank_lt` / `live_ordered`.

Replacing the rank by **well-foundedness of the live-arc relation** closes the
gap outright, with no pigeonhole, no topological order, and no finiteness.

The live-arc relation is read in the receiver-chasing direction:

  `LiveArc v u  ↔  Live u ∧ Live v ∧ 0 < mult u v`

so `Acc LiveArc x` says that chasing blocked senders forward from `x` terminates,
and `WellFounded LiveArc` says it terminates everywhere.

Three results:

* `wf_terminal_implies_ordinary_stable` — sufficiency, strictly generalizing
  `live_terminal_implies_ordinary_stable` (no `rank`, no `rank_lt`, no bound `n`);
* `filledSetOfNotWellFounded` — from `¬ WellFounded` a `FilledSet` is built
  directly, taking membership to be "not accessible";
* `wellFounded_iff_no_filled_set` — the two directions combine into an
  equivalence, so the ordering condition of the characterization is now proved
  rather than observed by census.

Note that a vertex that is not live is vacuously accessible, since every
`LiveArc y x` carries `Live x`.  So inaccessibility implies liveness and the
construction needs no extra hypothesis.

No declaration uses `sorry` or introduces an axiom beyond `propext` /
`Classical.choice` / `Quot.sound`, as `replay.py --build` records.
-/

namespace CBMDWeightedDynamics

/-- Receiver-to-sender relation on live vertices: `LiveArc v u` holds when `u`
sends to `v` and both are live. -/
def LiveArc {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat) (v u : Vertex n) : Prop :=
  Live outdegree capacity u ∧ Live outdegree capacity v ∧ 0 < mult u v

/-- A vertex that is not live is accessible for free: nothing is `LiveArc`-below it. -/
theorem acc_of_not_live {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    {w : Vertex n} (dead : ¬ Live outdegree capacity w) :
    Acc (LiveArc mult outdegree capacity) w :=
  Acc.intro w (fun _ hy => absurd hy.1 dead)

/-- Contrapositive of `acc_of_not_live`: an inaccessible vertex is live. -/
theorem live_of_not_acc {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    {w : Vertex n} (hw : ¬ Acc (LiveArc mult outdegree capacity) w) :
    Live outdegree capacity w := by
  classical
  by_cases h : Live outdegree capacity w
  · exact h
  · exact absurd (acc_of_not_live mult outdegree capacity h) hw

/-- **Sufficiency, with well-foundedness in place of a rank.**  Strictly more
general than `live_terminal_implies_ordinary_stable`: no rank function, and no
use of the bound `n` on vertex indices. -/
theorem wf_terminal_implies_ordinary_stable {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n)
    (admissible : ∀ v, chips v ≤ capacity v)
    (wf : WellFounded (LiveArc mult outdegree capacity))
    (live_closed : ∀ u v, Live outdegree capacity u → 0 < mult u v →
      Live outdegree capacity v)
    (live_bound : ∀ u v, Live outdegree capacity u → Live outdegree capacity v →
      0 < mult u v → outdegree v + mult u v ≤ capacity v + 1)
    (terminal : CapacityTerminal mult outdegree capacity chips) :
    OrdinaryStable outdegree chips := by
  classical
  intro u
  by_cases hu : Live outdegree capacity u
  · revert hu
    apply wf.induction u
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
      have h1 : capacity v + 1 ≤ chips v + mult w v := overflow
      have h2 : outdegree v + mult w v ≤ chips v + mult w v :=
        Nat.le_trans (live_bound w v hw hv hpos) h1
      have receiver_unstable : outdegree v ≤ chips v := Nat.le_of_add_le_add_right h2
      exact (Nat.not_lt_of_ge receiver_unstable) (later v ⟨hw, hv, hpos⟩ hv)
  · exact dead_is_ordinarily_stable outdegree capacity chips admissible hu

/-- From an inaccessible vertex there is always an arc to an inaccessible vertex. -/
theorem step_of_not_acc {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    {w : Vertex n} (hw : ¬ Acc (LiveArc mult outdegree capacity) w) :
    ∃ v, LiveArc mult outdegree capacity v w ∧
      ¬ Acc (LiveArc mult outdegree capacity) v := by
  classical
  refine Classical.byContradiction (fun hno => ?_)
  refine hw (Acc.intro w (fun v hv => ?_))
  by_cases hacc : Acc (LiveArc mult outdegree capacity) v
  · exact hacc
  · exact absurd ⟨v, hv, hacc⟩ hno

/-- Failure of well-foundedness produces an inaccessible vertex. -/
theorem exists_not_acc_of_not_wellFounded {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (not_wf : ¬ WellFounded (LiveArc mult outdegree capacity)) :
    ∃ w, ¬ Acc (LiveArc mult outdegree capacity) w := by
  classical
  refine Classical.byContradiction (fun hall => ?_)
  refine not_wf (WellFounded.intro (fun a => ?_))
  by_cases h : Acc (LiveArc mult outdegree capacity) a
  · exact h
  · exact absurd ⟨a, h⟩ hall

/-- **The converse direction.**  If the live-arc relation is not well founded then
a `FilledSet` exists, so `filled_set_obstruction` applies and preservation fails.
Membership is "not accessible"; `step_of_not_acc` supplies the successor map and
`live_of_not_acc` supplies the liveness of the witness.  No finiteness is used. -/
noncomputable def filledSetOfNotWellFounded {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (not_wf : ¬ WellFounded (LiveArc mult outdegree capacity)) :
    FilledSet mult outdegree capacity := by
  classical
  have hex := exists_not_acc_of_not_wellFounded mult outdegree capacity not_wf
  refine
    { mem := fun w => ¬ Acc (LiveArc mult outdegree capacity) w
      successor := fun w =>
        if h : ¬ Acc (LiveArc mult outdegree capacity) w then
          (step_of_not_acc mult outdegree capacity h).choose
        else w
      successor_mem := ?_
      successor_arc := ?_
      witness := hex.choose
      witness_mem := hex.choose_spec
      witness_live := live_of_not_acc mult outdegree capacity hex.choose_spec }
  · intro w hw _
    simp only [hw]
    exact (step_of_not_acc mult outdegree capacity hw).choose_spec.2
  · intro w hw _
    simp only [hw]
    exact ((step_of_not_acc mult outdegree capacity hw).choose_spec.1).2.2

/-- **Equivalence.**  Under live-closure, the live-arc relation is well founded
exactly when no `FilledSet` exists.  Together with
`wf_terminal_implies_ordinary_stable` and `filled_set_obstruction` this upgrades
the ordering condition of the characterization from an exhaustive census
observation to a proved equivalence. -/
theorem wellFounded_iff_no_filled_set {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (live_closed : ∀ u v, Live outdegree capacity u → 0 < mult u v →
      Live outdegree capacity v) :
    WellFounded (LiveArc mult outdegree capacity) ↔
      (FilledSet mult outdegree capacity → False) := by
  classical
  constructor
  · intro wf filled
    have key : ∀ w : Vertex n, filled.mem w → ¬ Live outdegree capacity w := by
      intro w
      apply wf.induction w
      intro z later memz livez
      have arc : 0 < mult z (filled.successor z) := filled.successor_arc z memz livez
      have memNext : filled.mem (filled.successor z) := filled.successor_mem z memz livez
      have liveNext : Live outdegree capacity (filled.successor z) :=
        live_closed z (filled.successor z) livez arc
      exact later (filled.successor z) ⟨livez, liveNext, arc⟩ memNext liveNext
    exact key filled.witness filled.witness_mem filled.witness_live
  · intro no_filled
    refine Classical.byContradiction (fun not_wf => ?_)
    exact no_filled (filledSetOfNotWellFounded mult outdegree capacity not_wf)

/-! ## Bridges to the previous formulation

The two lemmas below place the new hypothesis against the old ones.  The first
shows the rank hypotheses of `Characterization` imply well-foundedness, so
`wf_terminal_implies_ordinary_stable` subsumes
`live_terminal_implies_ordinary_stable`.  The second shows a directed cycle of
live vertices refutes it, which is the direction necessity needs.

What is deliberately **not** proved here is the reverse of the second: that a
finite live subgraph with no directed cycle is well founded.  That is the
classical finite-digraph fact, and it is no longer load-bearing — it describes
how the exhaustive census *decides* the hypothesis, not a step inside any
theorem. -/

/-- A rank that strictly increases along live arcs makes `LiveArc` well founded.
`live_terminal_implies_ordinary_stable` is therefore an instance of
`wf_terminal_implies_ordinary_stable`. -/
theorem wellFounded_of_rank {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (rank : Vertex n → Nat)
    (rank_lt : ∀ v, rank v < n)
    (live_ordered : ∀ u v, Live outdegree capacity u → Live outdegree capacity v →
      0 < mult u v → rank u < rank v) :
    WellFounded (LiveArc mult outdegree capacity) :=
  Subrelation.wf
    (fun {v u} (arc : LiveArc mult outdegree capacity v u) =>
      Nat.sub_lt_sub_left (rank_lt u) (live_ordered u v arc.1 arc.2.1 arc.2.2))
    (measure (fun w : Vertex n => n - rank w)).wf

/-- A closed cycle through live vertices refutes well-foundedness: it is already
a `FilledSet`, so the obstruction applies. -/
def filledSetOfLiveCycle {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (cycle : ClosedCycle mult)
    (cycle_live : ∀ v, cycle.onCycle v → Live outdegree capacity v) :
    FilledSet mult outdegree capacity where
  mem := cycle.onCycle
  successor := cycle.next
  successor_mem v hv _ := cycle.closed v hv
  successor_arc v hv _ := cycle.arc v hv
  witness := cycle.witness
  witness_mem := cycle.witness_mem
  witness_live := cycle_live _ cycle.witness_mem

theorem not_wellFounded_of_live_cycle {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (live_closed : ∀ u v, Live outdegree capacity u → 0 < mult u v →
      Live outdegree capacity v)
    (cycle : ClosedCycle mult)
    (cycle_live : ∀ v, cycle.onCycle v → Live outdegree capacity v) :
    ¬ WellFounded (LiveArc mult outdegree capacity) := by
  intro wf
  exact (wellFounded_iff_no_filled_set mult outdegree capacity live_closed).mp wf
    (filledSetOfLiveCycle mult outdegree capacity cycle cycle_live)

end CBMDWeightedDynamics
