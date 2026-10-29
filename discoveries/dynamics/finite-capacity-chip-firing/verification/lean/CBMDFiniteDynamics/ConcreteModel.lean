import CBMDFiniteDynamics.FullTheorem

/-!
# Concrete ordered-DAG chip firing

This module binds the abstract firing function in `FullTheorem.lean` to the
unit-edge chip update used by FD-C1.  It also proves ordinary termination for
that concrete update by the lexicographic order of chip counts in topological
vertex order.

Ordinary uniqueness is then proved from local commutation and a terminal-form
Newman lemma.  No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDFiniteDynamics

/-- Split a nonempty chip vector into its first coordinate and tail. -/
def splitChips {n : Nat} (chips : Chips (n + 1)) : Nat × Chips n :=
  (chips 0, fun v => chips v.succ)

/-- Lexicographic decrease in topological vertex order.  Earlier vertices are
more significant. -/
def ChipsLex : {n : Nat} → Chips n → Chips n → Prop
  | 0, _, _ => False
  | _n + 1, after, before =>
      Prod.Lex Nat.lt ChipsLex (splitChips after) (splitChips before)

theorem chipsLex_wellFounded : ∀ n, WellFounded (@ChipsLex n) := by
  intro n
  induction n with
  | zero =>
      exact WellFounded.intro fun state =>
        Acc.intro state fun _ impossible => False.elim impossible
  | succ n ih =>
      let pairWf : WellFounded
          (Prod.Lex Nat.lt (@ChipsLex n)) :=
        WellFounded.intro fun pair =>
          Prod.lexAccessible
            (WellFounded.apply Nat.lt_wfRel.wf pair.1)
            (WellFounded.apply ih)
            pair.2
      exact InvImage.wf splitChips pairWf

/-- A decrease at one coordinate, with all earlier coordinates unchanged,
implies lexicographic decrease. -/
theorem chipsLex_of_pivot {n : Nat}
    (after before : Chips n) (pivot : Vertex n)
    (earlier_eq : ∀ v, v.val < pivot.val → after v = before v)
    (pivot_lt : after pivot < before pivot) :
    ChipsLex after before := by
  induction n with
  | zero => exact Fin.elim0 pivot
  | succ n ih =>
      by_cases pivot_zero : pivot = 0
      · subst pivot
        exact Prod.Lex.left _ _ pivot_lt
      · rcases Fin.eq_succ_of_ne_zero pivot_zero with ⟨tailPivot, rfl⟩
        have head_eq : after 0 = before 0 :=
          earlier_eq 0 (Fin.succ_pos tailPivot)
        rw [ChipsLex, splitChips, head_eq]
        apply Prod.Lex.right (before 0)
        apply ih
        · intro v hv
          exact earlier_eq v.succ (Nat.succ_lt_succ hv)
        · exact pivot_lt

/-- Concrete unit-edge firing.  The outdegree includes all nonsink edges and
any chips lost to the absorbing sink; the Boolean branch here represents only
the unit nonsink transfers. -/
def concreteFire {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    (chips : Chips n) (u : Vertex n) : Chips n :=
  fun v =>
    if v = u then chips v - outdegree u
    else if edge u v then chips v + 1
    else chips v

theorem concreteFire_at_source {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    (chips : Chips n) (u : Vertex n) :
    concreteFire edge outdegree chips u u = chips u - outdegree u := by
  simp [concreteFire]

theorem concreteFire_earlier_unchanged {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    (chips : Chips n) (u v : Vertex n)
    (edge_order : TopologicallyOrdered edge)
    (earlier : v.val < u.val) :
    concreteFire edge outdegree chips u v = chips v := by
  have v_ne_u : v ≠ u := by
    intro equal
    subst v
    exact (Nat.lt_irrefl u.val earlier)
  have no_edge : ¬ edge u v := by
    intro huv
    exact (Nat.not_lt_of_ge (Nat.le_of_lt earlier)) (edge_order huv)
  simp [concreteFire, v_ne_u, no_edge]

/-- Every concrete ordinary firing strictly decreases the chip vector in
topological lexicographic order. -/
theorem concrete_ordinary_step_decreases {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    (edge_order : TopologicallyOrdered edge)
    (outdegree_pos : ∀ u, 0 < outdegree u)
    {before after : Chips n}
    (step : OrdinaryStep (concreteFire edge outdegree) outdegree before after) :
    ChipsLex after before := by
  rcases step with ⟨u, unstable, rfl⟩
  apply chipsLex_of_pivot (pivot := u)
  · intro v earlier
    exact concreteFire_earlier_unchanged
      edge outdegree before u v edge_order earlier
  · rw [concreteFire_at_source]
    exact Nat.sub_lt_of_pos_le (outdegree_pos u) unstable

theorem concrete_ordinary_wellFounded {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    (edge_order : TopologicallyOrdered edge)
    (outdegree_pos : ∀ u, 0 < outdegree u) :
    WellFounded (fun after before =>
      OrdinaryStep (concreteFire edge outdegree) outdegree before after) := by
  exact Subrelation.wf
    (fun step => concrete_ordinary_step_decreases
      edge outdegree edge_order outdegree_pos step)
    (chipsLex_wellFounded n)

namespace Reaches

theorem trans {α : Sort _} {step : α → α → Prop} {x y z : α}
    (first : Reaches step x y) (second : Reaches step y z) :
    Reaches step x z := by
  induction second with
  | refl => exact first
  | tail path last ih => exact Reaches.tail ih last

theorem eq_or_head {α : Sort _} {step : α → α → Prop} {x z : α}
    (path : Reaches step x z) :
    x = z ∨ ∃ y, step x y ∧ Reaches step y z := by
  induction path with
  | refl => exact Or.inl rfl
  | tail path last ih =>
      cases ih with
      | inl equal =>
          subst_vars
          exact Or.inr ⟨_, last, Reaches.refl _⟩
      | inr witness =>
          rcases witness with ⟨next, first, rest⟩
          exact Or.inr ⟨next, first, Reaches.tail rest last⟩

end Reaches

theorem terminal_reaches_eq {α : Sort _} {step : α → α → Prop}
    {x y : α} (terminal : Terminal step x) (path : Reaches step x y) :
    y = x := by
  cases Reaches.eq_or_head path with
  | inl equal => exact equal.symm
  | inr witness =>
      rcases witness with ⟨next, first, _⟩
      exact (terminal next first).elim

/-- Newman's lemma in the terminal-uniqueness form needed here. -/
theorem newman_terminal_unique {α : Sort _}
    (step : α → α → Prop)
    (step_wf : WellFounded (fun after before => step before after))
    (locally_joinable : ∀ {x y z}, step x y → step x z →
      ∃ common, Reaches step y common ∧ Reaches step z common)
    {initial left right : α}
    (left_path : Reaches step initial left)
    (left_terminal : Terminal step left)
    (right_path : Reaches step initial right)
    (right_terminal : Terminal step right) :
    left = right := by
  induction initial using step_wf.induction generalizing left right with
  | h initial normalize_later =>
      cases Reaches.eq_or_head left_path with
      | inl left_is_initial =>
          subst left
          exact (terminal_reaches_eq left_terminal right_path).symm
      | inr left_head =>
          rcases left_head with ⟨leftNext, firstLeft, restLeft⟩
          cases Reaches.eq_or_head right_path with
          | inl right_is_initial =>
              subst right
              exact terminal_reaches_eq right_terminal left_path
          | inr right_head =>
              rcases right_head with ⟨rightNext, firstRight, restRight⟩
              rcases locally_joinable firstLeft firstRight with
                ⟨common, left_join, right_join⟩
              rcases exists_reachable_terminal step step_wf common with
                ⟨normal, common_path, normal_terminal⟩
              have left_to_normal : Reaches step leftNext normal :=
                Reaches.trans left_join common_path
              have right_to_normal : Reaches step rightNext normal :=
                Reaches.trans right_join common_path
              have left_eq : left = normal :=
                normalize_later leftNext firstLeft
                  restLeft left_terminal left_to_normal normal_terminal
              have right_eq : right = normal :=
                normalize_later rightNext firstRight
                  restRight right_terminal right_to_normal normal_terminal
              exact left_eq.trans right_eq.symm

theorem concreteFire_preserves_other_unstable {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    (chips : Chips n) (u v : Vertex n)
    (distinct : u ≠ v)
    (unstable : OrdinaryUnstable outdegree chips v) :
    OrdinaryUnstable outdegree (concreteFire edge outdegree chips u) v := by
  unfold OrdinaryUnstable at unstable ⊢
  by_cases incoming : edge u v
  · simp [concreteFire, distinct.symm, incoming]
    exact Nat.le_trans unstable (Nat.le_add_right (chips v) 1)
  · simp [concreteFire, distinct.symm, incoming]
    exact unstable

theorem concreteFire_commutes {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    (chips : Chips n) (u v : Vertex n)
    (distinct : u ≠ v)
    (u_unstable : OrdinaryUnstable outdegree chips u)
    (v_unstable : OrdinaryUnstable outdegree chips v) :
    concreteFire edge outdegree (concreteFire edge outdegree chips u) v =
      concreteFire edge outdegree (concreteFire edge outdegree chips v) u := by
  unfold OrdinaryUnstable at u_unstable v_unstable
  funext w
  by_cases w_eq_u : w = u
  · subst w
    by_cases incoming : edge v u
    · simp [concreteFire, distinct, incoming]
      omega
    · simp [concreteFire, distinct, incoming]
  · by_cases w_eq_v : w = v
    · subst w
      by_cases incoming : edge u v
      · simp [concreteFire, distinct.symm, incoming]
        omega
      · simp [concreteFire, distinct.symm, incoming]
    · by_cases from_u : edge u w
      · by_cases from_v : edge v w
        · simp [concreteFire, w_eq_u, w_eq_v, from_u, from_v]
        · simp [concreteFire, w_eq_u, w_eq_v, from_u, from_v]
      · by_cases from_v : edge v w
        · simp [concreteFire, w_eq_u, w_eq_v, from_u, from_v]
        · simp [concreteFire, w_eq_u, w_eq_v, from_u, from_v]

theorem concrete_ordinary_locally_joinable {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    {before left right : Chips n}
    (left_step :
      OrdinaryStep (concreteFire edge outdegree) outdegree before left)
    (right_step :
      OrdinaryStep (concreteFire edge outdegree) outdegree before right) :
    ∃ common,
      Reaches (OrdinaryStep (concreteFire edge outdegree) outdegree)
        left common ∧
      Reaches (OrdinaryStep (concreteFire edge outdegree) outdegree)
        right common := by
  rcases left_step with ⟨u, u_unstable, rfl⟩
  rcases right_step with ⟨v, v_unstable, rfl⟩
  by_cases same : u = v
  · subst v
    exact ⟨concreteFire edge outdegree before u,
      Reaches.refl _, Reaches.refl _⟩
  · let common :=
      concreteFire edge outdegree
        (concreteFire edge outdegree before u) v
    have v_still_unstable :
        OrdinaryUnstable outdegree
          (concreteFire edge outdegree before u) v :=
      concreteFire_preserves_other_unstable
        edge outdegree before u v same v_unstable
    have u_still_unstable :
        OrdinaryUnstable outdegree
          (concreteFire edge outdegree before v) u :=
      concreteFire_preserves_other_unstable
        edge outdegree before v u (Ne.symm same) u_unstable
    have commute := concreteFire_commutes
      edge outdegree before u v same u_unstable v_unstable
    refine ⟨common, ?_, ?_⟩
    · exact Reaches.tail (Reaches.refl _)
        ⟨v, v_still_unstable, rfl⟩
    · exact Reaches.tail (Reaches.refl _)
        ⟨u, u_still_unstable, commute.symm⟩

theorem concrete_ordinary_terminal_iff_stable {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat) (chips : Chips n) :
    Terminal (OrdinaryStep (concreteFire edge outdegree) outdegree) chips ↔
      OrdinaryStable outdegree chips := by
  constructor
  · intro terminal v
    by_cases unstable : outdegree v ≤ chips v
    · exact (terminal (concreteFire edge outdegree chips v)
        ⟨v, unstable, rfl⟩).elim
    · exact Nat.lt_of_not_ge unstable
  · intro stable after step
    rcases step with ⟨u, unstable, _⟩
    exact (Nat.not_lt_of_ge unstable) (stable u)

/-- The concrete ordinary ordered-DAG system has a reachable stable state, and
every reachable stable state is equal to it. -/
theorem concrete_ordinary_unique_stabilization {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree : Vertex n → Nat)
    (initial : Chips n)
    (edge_order : TopologicallyOrdered edge)
    (outdegree_pos : ∀ u, 0 < outdegree u) :
    ∃ ordinaryNormal,
      Reaches (OrdinaryStep (concreteFire edge outdegree) outdegree)
        initial ordinaryNormal ∧
      OrdinaryStable outdegree ordinaryNormal ∧
      ∀ state,
        Reaches (OrdinaryStep (concreteFire edge outdegree) outdegree)
          initial state →
        OrdinaryStable outdegree state → state = ordinaryNormal := by
  let step := OrdinaryStep (concreteFire edge outdegree) outdegree
  have step_wf : WellFounded (fun after before => step before after) :=
    concrete_ordinary_wellFounded
      edge outdegree edge_order outdegree_pos
  rcases exists_reachable_terminal step step_wf initial with
    ⟨ordinaryNormal, normal_path, normal_terminal⟩
  have normal_stable : OrdinaryStable outdegree ordinaryNormal :=
    (concrete_ordinary_terminal_iff_stable
      edge outdegree ordinaryNormal).mp normal_terminal
  refine ⟨ordinaryNormal, normal_path, normal_stable, ?_⟩
  intro state state_path state_stable
  have state_terminal : Terminal step state :=
    (concrete_ordinary_terminal_iff_stable
      edge outdegree state).mpr state_stable
  exact newman_terminal_unique step step_wf
    (fun first second =>
      concrete_ordinary_locally_joinable edge outdegree first second)
    state_path state_terminal normal_path normal_terminal

/-- FD-C1 specialized to the concrete unit-edge update.  Ordinary termination
is now discharged internally; ordinary uniqueness remains the sole explicit
interface. -/
theorem fd_c1_concrete_transfer {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree capacity : Vertex n → Nat)
    (initial ordinaryNormal : Chips n)
    (edge_order : TopologicallyOrdered edge)
    (outdegree_pos : ∀ u, 0 < outdegree u)
    (capacity_ge_outdegree : ∀ v, outdegree v ≤ capacity v)
    (ordinary_unique : ∀ state,
      Reaches (OrdinaryStep (concreteFire edge outdegree) outdegree)
        initial state →
      OrdinaryStable outdegree state → state = ordinaryNormal) :
    (∃ final,
      Reaches
        (CapacityStep edge (concreteFire edge outdegree)
          outdegree capacity)
        initial final ∧
      CapacityTerminal edge outdegree capacity final ∧
      final = ordinaryNormal) ∧
    (∀ final,
      Reaches
        (CapacityStep edge (concreteFire edge outdegree)
          outdegree capacity)
        initial final →
      CapacityTerminal edge outdegree capacity final →
      final = ordinaryNormal) := by
  exact fd_c1_transfer
    edge (concreteFire edge outdegree) outdegree capacity
    initial ordinaryNormal edge_order capacity_ge_outdegree
    (concrete_ordinary_wellFounded
      edge outdegree edge_order outdegree_pos)
    ordinary_unique

/-- Fully concrete FD-C1 theorem for the ordered unit-edge update.  Both
ordinary termination and ordinary uniqueness are discharged internally. -/
theorem fd_c1_concrete {n : Nat}
    (edge : Vertex n → Vertex n → Prop) [DecidableRel edge]
    (outdegree capacity : Vertex n → Nat)
    (initial : Chips n)
    (edge_order : TopologicallyOrdered edge)
    (outdegree_pos : ∀ u, 0 < outdegree u)
    (capacity_ge_outdegree : ∀ v, outdegree v ≤ capacity v) :
    ∃ ordinaryNormal,
      Reaches (OrdinaryStep (concreteFire edge outdegree) outdegree)
        initial ordinaryNormal ∧
      OrdinaryStable outdegree ordinaryNormal ∧
      (∃ final,
        Reaches
          (CapacityStep edge (concreteFire edge outdegree)
            outdegree capacity)
          initial final ∧
        CapacityTerminal edge outdegree capacity final ∧
        final = ordinaryNormal) ∧
      (∀ final,
        Reaches
          (CapacityStep edge (concreteFire edge outdegree)
            outdegree capacity)
          initial final →
        CapacityTerminal edge outdegree capacity final →
        final = ordinaryNormal) := by
  rcases concrete_ordinary_unique_stabilization
      edge outdegree initial edge_order outdegree_pos with
    ⟨ordinaryNormal, ordinary_path, ordinary_stable, ordinary_unique⟩
  rcases fd_c1_concrete_transfer
      edge outdegree capacity initial ordinaryNormal
      edge_order outdegree_pos capacity_ge_outdegree ordinary_unique with
    ⟨capacity_exists, capacity_unique⟩
  exact ⟨ordinaryNormal, ordinary_path, ordinary_stable,
    capacity_exists, capacity_unique⟩

end CBMDFiniteDynamics
