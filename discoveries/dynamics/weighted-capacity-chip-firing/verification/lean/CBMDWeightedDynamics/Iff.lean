import CBMDWeightedDynamics.Equivalence
import CBMDWeightedDynamics.Necessity
import CBMDWeightedDynamics.FiniteAcyclic

/-!
# The characterization as one compiled equivalence

Revisions 0.3.0–0.5.0 proved sufficiency of the three live-set conditions,
necessity of the bound and of live-closure, and that well-foundedness is
equivalent to the absence of filled sets.  The pieces were never assembled,
so the dossier still listed "exactness of the full three-condition predicate"
as a census result.  This module assembles them:

    TerminalStable  ↔  WellFounded LiveArc ∧ live-closed ∧ live-bound

where `TerminalStable` says every admissible capacity-terminal state is
ordinarily stable — the conclusion the sufficiency theorem proves and the
obstructions refute.  Only positive outdegree is assumed.
-/

namespace CBMDWeightedDynamics

variable {n : Nat} (mult : Vertex n → Vertex n → Nat) (outdegree capacity : Vertex n → Nat)

def TerminalStable : Prop :=
  ∀ chips : Chips n, (∀ v, chips v ≤ capacity v) →
    CapacityTerminal mult outdegree capacity chips → OrdinaryStable outdegree chips

def LiveClosed : Prop :=
  ∀ u v, Live outdegree capacity u → 0 < mult u v → Live outdegree capacity v

def LiveBound : Prop :=
  ∀ u v, Live outdegree capacity u → Live outdegree capacity v →
    0 < mult u v → outdegree v + mult u v ≤ capacity v + 1

/-- A filled set refutes terminal stability. -/
theorem not_terminalStable_of_filled (pos : ∀ u, 0 < outdegree u)
    (F : FilledSet mult outdegree capacity) : ¬ TerminalStable mult outdegree capacity := by
  classical
  intro ts
  let chips : Chips n := fun v => if F.mem v then capacity v else 0
  have adm : ∀ v, chips v ≤ capacity v := by
    intro v; simp only [chips]; split <;> omega
  obtain ⟨term, unstable⟩ := filled_set_obstruction mult outdegree capacity F pos chips
    (fun v h => by simp [chips, h]) (fun v h => by simp [chips, h])
  exact unstable (ts chips adm term)

theorem terminalStable_iff (pos : ∀ u, 0 < outdegree u) :
    TerminalStable mult outdegree capacity ↔
      WellFounded (LiveArc mult outdegree capacity) ∧ LiveClosed mult outdegree capacity ∧
        LiveBound mult outdegree capacity := by
  constructor
  · intro ts
    have closed : LiveClosed mult outdegree capacity := by
      intro u v hu arc
      apply Classical.byContradiction
      intro hv
      exact not_terminalStable_of_filled mult outdegree capacity pos
        (liveToDeadFilledSet mult outdegree capacity hu hv arc) ts
    have wf : WellFounded (LiveArc mult outdegree capacity) :=
      (wellFounded_iff_no_filled_set mult outdegree capacity closed).mpr
        (fun F => not_terminalStable_of_filled mult outdegree capacity pos F ts)
    refine ⟨wf, closed, ?_⟩
    intro u v hu hv arc
    apply Classical.byContradiction
    intro hviol
    have violated : capacity v + 1 < outdegree v + mult u v := by omega
    by_cases e : u = v
    · subst e
      -- a live self-loop is a LiveArc cycle, impossible under well-foundedness
      have self : LiveArc mult outdegree capacity u u := ⟨hu, hu, arc⟩
      have irr : ∀ x, Acc (LiveArc mult outdegree capacity) x →
          ¬ LiveArc mult outdegree capacity x x := by
        intro x acc
        induction acc with
        | intro x _ ih => exact fun h => ih x h h
      exact irr u (wf.apply u) self
    · classical
      let chips : Chips n := fun w =>
        if w = u then capacity u else if w = v then capacity v + 1 - mult u v else 0
      have adm : ∀ w, chips w ≤ capacity w := by
        intro w
        simp only [chips]
        split
        · rename_i h; subst h; omega
        split
        · rename_i h; subst h; omega
        · omega
      have hne : v ≠ u := fun h => e h.symm
      obtain ⟨term, unstable⟩ := bound_violation_defeats_transfer mult outdegree capacity pos
        hu arc violated chips (by simp [chips]) (by simp [chips, hne])
        (fun w h1 h2 => by simp [chips, h1, h2]) e
      exact unstable (ts chips adm term)
  · intro ⟨wf, closed, bound⟩ chips adm term
    exact wf_terminal_implies_ordinary_stable mult outdegree capacity chips adm wf closed bound term

/-- The same characterization with the ordering condition read as acyclicity of
the live subgraph — the form an exhaustive census decides by cycle detection. -/
theorem terminalStable_iff_acyclic (pos : ∀ u, 0 < outdegree u) :
    TerminalStable mult outdegree capacity ↔
      (∀ x, ¬ Relation.TransGen (LiveArc mult outdegree capacity) x x) ∧
        LiveClosed mult outdegree capacity ∧ LiveBound mult outdegree capacity := by
  rw [terminalStable_iff mult outdegree capacity pos,
    liveArc_wellFounded_iff_acyclic mult outdegree capacity]

end CBMDWeightedDynamics
