import CBMDWeightedDynamics.Transfer

/-!
# The weighted transfer theorem, fully concrete

`weighted_transfer` takes the firing function as a parameter and the ordinary
theory — termination and uniqueness of ordinary stabilization — as two
explicit hypotheses.  This module binds the firing function to the concrete
multigraph update (the fired vertex loses `outdegree u`; each `v` gains
`mult u v`) and proves both hypotheses for ordered multigraphs, following the
unit-edge predecessor's argument: lexicographic descent in topological order
for termination, local commutation and a terminal form of Newman's lemma for
uniqueness.  The result is the weighted transfer theorem with no ordinary
hypotheses left.
-/

namespace CBMDWeightedDynamics

/-- Concrete multigraph firing. -/
def wFire {n : Nat} (mult : Vertex n → Vertex n → Nat) (outdegree : Vertex n → Nat)
    (chips : Chips n) (u : Vertex n) : Chips n :=
  fun v => if v = u then chips v - outdegree u else chips v + mult u v

/-! ## Termination -/

def splitChips {n : Nat} (chips : Chips (n + 1)) : Nat × Chips n :=
  (chips 0, fun v => chips v.succ)

def ChipsLex : {n : Nat} → Chips n → Chips n → Prop
  | 0, _, _ => False
  | _n + 1, after, before => Prod.Lex Nat.lt ChipsLex (splitChips after) (splitChips before)

theorem chipsLex_wellFounded : ∀ n, WellFounded (@ChipsLex n) := by
  intro n
  induction n with
  | zero => exact WellFounded.intro fun s => Acc.intro s fun _ h => False.elim h
  | succ n ih =>
    let pairWf : WellFounded (Prod.Lex Nat.lt (@ChipsLex n)) :=
      WellFounded.intro fun pair =>
        Prod.lexAccessible (WellFounded.apply Nat.lt_wfRel.wf pair.1) (WellFounded.apply ih) pair.2
    exact InvImage.wf splitChips pairWf

theorem chipsLex_of_pivot {n : Nat} (after before : Chips n) (pivot : Vertex n)
    (earlier_eq : ∀ v, v.val < pivot.val → after v = before v)
    (pivot_lt : after pivot < before pivot) : ChipsLex after before := by
  induction n with
  | zero => exact Fin.elim0 pivot
  | succ n ih =>
    by_cases pivot_zero : pivot = 0
    · subst pivot
      exact Prod.Lex.left _ _ pivot_lt
    · rcases Fin.eq_succ_of_ne_zero pivot_zero with ⟨tailPivot, rfl⟩
      have head_eq : after 0 = before 0 := earlier_eq 0 (Fin.succ_pos tailPivot)
      rw [ChipsLex, splitChips, head_eq]
      apply Prod.Lex.right (before 0)
      apply ih
      · intro v hv; exact earlier_eq v.succ (Nat.succ_lt_succ hv)
      · exact pivot_lt

theorem wFire_earlier_unchanged {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree : Vertex n → Nat) (chips : Chips n) (u v : Vertex n)
    (order : TopologicallyOrdered mult) (earlier : v.val < u.val) :
    wFire mult outdegree chips u v = chips v := by
  have ne : v ≠ u := fun h => by subst h; exact Nat.lt_irrefl _ earlier
  have zero : mult u v = 0 := by
    apply Classical.byContradiction
    intro h
    have := order (Nat.pos_of_ne_zero h)
    omega
  simp [wFire, ne, zero]

theorem wFire_wellFounded {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree : Vertex n → Nat) (order : TopologicallyOrdered mult)
    (pos : ∀ u, 0 < outdegree u) :
    WellFounded (fun after before => OrdinaryStep (wFire mult outdegree) outdegree before after) := by
  apply Subrelation.wf _ (chipsLex_wellFounded n)
  intro after before step
  rcases step with ⟨u, unstable, rfl⟩
  apply chipsLex_of_pivot (pivot := u)
  · intro v earlier; exact wFire_earlier_unchanged mult outdegree before u v order earlier
  · simp only [wFire, ite_true]
    exact Nat.sub_lt_of_pos_le (pos u) unstable

/-! ## Uniqueness -/

theorem reaches_trans {α : Sort _} {step : α → α → Prop} {x y z : α}
    (first : Reaches step x y) (second : Reaches step y z) : Reaches step x z := by
  induction second with
  | refl => exact first
  | tail _ last ih => exact Reaches.tail ih last

theorem reaches_eq_or_head {α : Sort _} {step : α → α → Prop} {x z : α}
    (path : Reaches step x z) : x = z ∨ ∃ y, step x y ∧ Reaches step y z := by
  induction path with
  | refl => exact Or.inl rfl
  | tail _ last ih =>
    rcases ih with e | ⟨next, first, rest⟩
    · subst e; exact Or.inr ⟨_, last, Reaches.refl _⟩
    · exact Or.inr ⟨next, first, Reaches.tail rest last⟩

theorem terminal_reaches_eq {α : Sort _} {step : α → α → Prop} {x y : α}
    (terminal : Terminal step x) (path : Reaches step x y) : y = x := by
  rcases reaches_eq_or_head path with e | ⟨next, first, _⟩
  · exact e.symm
  · exact (terminal next first).elim

theorem newman_terminal_unique {α : Sort _} (step : α → α → Prop)
    (step_wf : WellFounded (fun after before => step before after))
    (joinable : ∀ {x y z}, step x y → step x z →
      ∃ common, Reaches step y common ∧ Reaches step z common)
    {initial left right : α}
    (lp : Reaches step initial left) (lt : Terminal step left)
    (rp : Reaches step initial right) (rt : Terminal step right) : left = right := by
  induction initial using step_wf.induction generalizing left right with
  | h initial ih =>
    rcases reaches_eq_or_head lp with e | ⟨ln, lf, lr⟩
    · subst e; exact (terminal_reaches_eq lt rp).symm
    rcases reaches_eq_or_head rp with e | ⟨rn, rf, rr⟩
    · subst e; exact terminal_reaches_eq rt lp
    obtain ⟨common, lj, rj⟩ := joinable lf rf
    obtain ⟨normal, cp, nt⟩ := exists_reachable_terminal step step_wf common
    have l := ih ln lf lr lt (reaches_trans lj cp) nt
    have r := ih rn rf rr rt (reaches_trans rj cp) nt
    exact l.trans r.symm

theorem wFire_preserves_other_unstable {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree : Vertex n → Nat) (chips : Chips n) (u v : Vertex n) (ne : u ≠ v)
    (unstable : OrdinaryUnstable outdegree chips v) :
    OrdinaryUnstable outdegree (wFire mult outdegree chips u) v := by
  unfold OrdinaryUnstable at unstable ⊢
  simp only [wFire, ne.symm, ite_false]
  omega

theorem wFire_commutes {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree : Vertex n → Nat) (chips : Chips n) (u v : Vertex n) (ne : u ≠ v)
    (hu : OrdinaryUnstable outdegree chips u) (hv : OrdinaryUnstable outdegree chips v) :
    wFire mult outdegree (wFire mult outdegree chips u) v =
      wFire mult outdegree (wFire mult outdegree chips v) u := by
  unfold OrdinaryUnstable at hu hv
  funext w
  by_cases wu : w = u
  · subst wu; simp [wFire, ne]; omega
  · by_cases wv : w = v
    · subst wv; simp [wFire, ne.symm]; omega
    · simp [wFire, wu, wv]; omega

theorem wFire_locally_joinable {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree : Vertex n → Nat) {before left right : Chips n}
    (ls : OrdinaryStep (wFire mult outdegree) outdegree before left)
    (rs : OrdinaryStep (wFire mult outdegree) outdegree before right) :
    ∃ common, Reaches (OrdinaryStep (wFire mult outdegree) outdegree) left common ∧
      Reaches (OrdinaryStep (wFire mult outdegree) outdegree) right common := by
  rcases ls with ⟨u, hu, rfl⟩
  rcases rs with ⟨v, hv, rfl⟩
  by_cases same : u = v
  · subst same; exact ⟨_, Reaches.refl _, Reaches.refl _⟩
  · refine ⟨wFire mult outdegree (wFire mult outdegree before u) v, ?_, ?_⟩
    · exact Reaches.tail (Reaches.refl _)
        ⟨v, wFire_preserves_other_unstable mult outdegree before u v same hv, rfl⟩
    · exact Reaches.tail (Reaches.refl _)
        ⟨u, wFire_preserves_other_unstable mult outdegree before v u (Ne.symm same) hu,
          (wFire_commutes mult outdegree before u v same hu hv).symm⟩

theorem wFire_terminal_iff_stable {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree : Vertex n → Nat) (chips : Chips n) :
    Terminal (OrdinaryStep (wFire mult outdegree) outdegree) chips ↔
      OrdinaryStable outdegree chips := by
  constructor
  · intro terminal v
    by_cases unstable : outdegree v ≤ chips v
    · exact (terminal _ ⟨v, unstable, rfl⟩).elim
    · exact Nat.lt_of_not_ge unstable
  · intro stable after ⟨u, unstable, _⟩
    exact (Nat.not_lt_of_ge unstable) (stable u)

/-- Ordinary stabilization of an ordered multigraph exists and is unique. -/
theorem wFire_unique_stabilization {n : Nat} (mult : Vertex n → Vertex n → Nat)
    (outdegree : Vertex n → Nat) (initial : Chips n) (order : TopologicallyOrdered mult)
    (pos : ∀ u, 0 < outdegree u) :
    ∃ normal, Reaches (OrdinaryStep (wFire mult outdegree) outdegree) initial normal ∧
      OrdinaryStable outdegree normal ∧
      ∀ state, Reaches (OrdinaryStep (wFire mult outdegree) outdegree) initial state →
        OrdinaryStable outdegree state → state = normal := by
  let step := OrdinaryStep (wFire mult outdegree) outdegree
  have wf := wFire_wellFounded mult outdegree order pos
  obtain ⟨normal, np, nt⟩ := exists_reachable_terminal step wf initial
  refine ⟨normal, np, (wFire_terminal_iff_stable mult outdegree normal).mp nt, ?_⟩
  intro state sp ss
  exact newman_terminal_unique step wf (fun a b => wFire_locally_joinable mult outdegree a b)
    sp ((wFire_terminal_iff_stable mult outdegree state).mpr ss) np nt

/-- **The weighted transfer theorem, fully concrete.**  For an ordered
multigraph satisfying the weighted bound, capacity-blocked firing reaches the
ordinary normal form, and every capacity-terminal state reachable from the
initial state is that normal form.  No ordinary-theory hypothesis remains. -/
theorem weighted_transfer_concrete {n : Nat}
    (mult : Vertex n → Vertex n → Nat) (outdegree capacity incomingBound : Vertex n → Nat)
    (initial : Chips n)
    (order : TopologicallyOrdered mult)
    (pos : ∀ u, 0 < outdegree u)
    (mult_le : ∀ u v, mult u v ≤ incomingBound v)
    (admits : CapacityAdmits outdegree capacity incomingBound) :
    ∃ normal,
      Reaches (OrdinaryStep (wFire mult outdegree) outdegree) initial normal ∧
      OrdinaryStable outdegree normal ∧
      (∃ final,
        Reaches (CapacityStep mult (wFire mult outdegree) outdegree capacity) initial final ∧
        CapacityTerminal mult outdegree capacity final ∧ final = normal) ∧
      (∀ final,
        Reaches (CapacityStep mult (wFire mult outdegree) outdegree capacity) initial final →
        CapacityTerminal mult outdegree capacity final → final = normal) := by
  obtain ⟨normal, np, ns, unique⟩ := wFire_unique_stabilization mult outdegree initial order pos
  obtain ⟨ex, all⟩ := weighted_transfer mult (wFire mult outdegree) outdegree capacity
    incomingBound initial normal order mult_le admits (wFire_wellFounded mult outdegree order pos)
    unique
  exact ⟨normal, np, ns, ex, all⟩

end CBMDWeightedDynamics
