import CBMDPetriCapacity.Core

/-!
# Conflict-free nets: a bad marking is a chain of forced overflows

Revision 0.12.0 decides preservation for conflict-free nets — every place has
at most one consuming transition — when every transition has an input place.
This module compiles the characterization behind that procedure:

    ¬ Preserves N cap  ↔  ∃ t0 R,  pre t0 ≤ cap  ∧  R t0  ∧  Closed t0 R

where `Closed t0 R` says each member of `R` has an *option*: an output place
and a value at which it overflows, such that the chain either *ends* there or
the place's consumer is again in `R`.  The right-hand side is a post-fixpoint
condition, so it is decided by computing a greatest fixpoint.

**Completeness** takes `R` to be the transitions ordinarily enabled at a bad
marking.  **Soundness** follows one chosen option per member from `t0`; the
transitions so visited form a single chain, so at most one of them takes an
ending option, and the marking that raises only the chosen places blocks
everything.  The two hypotheses enter exactly where the written argument says:
conflict-freeness makes the visited chain deterministic and gives each place a
unique consumer, and the input-place hypothesis supplies a low input for every
transition off the chain.
-/

namespace CBMDPetriCapacity

namespace ConflictFree

variable {P T : Nat} (N : Net P T) (cap : Fin P → Nat)

def IsConflictFree : Prop := ∀ q t t', 0 < N.pre t q → 0 < N.pre t' q → t = t'

def HasInput : Prop := ∀ t, ∃ q, 0 < N.pre t q

/-- `t` overflows at `q` with value `v`, inside the box and above `t0`'s floor. -/
def Opt (t0 t : Fin T) (q : Fin P) (v : Nat) : Prop :=
  v ≤ cap q ∧ N.pre t0 q ≤ v ∧ cap q < v - N.pre t q + N.post t q

/-- The chain ends at `q`: no consumer, or the consumer is `t` or `t0`, or the
consumer has another input, or the consumer's own lower literal holds at `v`. -/
def Ends (t0 t : Fin T) (q : Fin P) (v : Nat) : Prop :=
  (∀ c, N.pre c q = 0) ∨ 0 < N.pre t q ∨ 0 < N.pre t0 q ∨
    (∃ c r, 0 < N.pre c q ∧ 0 < N.pre c r ∧ r ≠ q) ∨ (∃ c, 0 < N.pre c q ∧ v < N.pre c q)

def Closed (t0 : Fin T) (R : Fin T → Prop) : Prop :=
  ∀ t, R t → ∃ q v, Opt N cap t0 t q v ∧ (Ends N t0 t q v ∨ ∀ c, 0 < N.pre c q → R c)

/-- The certificate. -/
def Certificate : Prop :=
  ∃ t0 R, (∀ q, N.pre t0 q ≤ cap q) ∧ R t0 ∧ Closed N cap t0 R

theorem not_preserves_iff_bad :
    ¬ Preserves N cap ↔ ∃ m, Admissible cap m ∧ CapDead N cap m ∧ ∃ t, OrdEnabled N m t := by
  constructor
  · intro np
    apply Classical.byContradiction
    intro h
    apply np
    intro m adm dead t ord
    exact h ⟨m, adm, dead, t, ord⟩
  · intro ⟨m, adm, dead, t, ord⟩ pres
    exact pres m adm dead t ord

/-! ## Completeness -/

theorem certificate_of_bad {m : Marking P} (adm : Admissible cap m)
    (dead : CapDead N cap m) {t0 : Fin T} (ord0 : OrdEnabled N m t0) :
    Certificate N cap := by
  refine ⟨t0, fun t => OrdEnabled N m t, fun q => Nat.le_trans (ord0 q) (adm q), ord0, ?_⟩
  intro t ordt
  have : ¬ ∀ q, m q - N.pre t q + N.post t q ≤ cap q := fun fits => dead t ⟨ordt, fits⟩
  have ⟨q, hq⟩ : ∃ q, ¬ (m q - N.pre t q + N.post t q ≤ cap q) :=
    Classical.byContradiction fun h => this fun q => Classical.byContradiction fun hq => h ⟨q, hq⟩
  refine ⟨q, m q, ⟨adm q, ord0 q, by omega⟩, ?_⟩
  apply Classical.byContradiction
  intro hno
  apply hno
  right
  intro c hc
  -- not ending: c is single-input with its literal failing, so it is enabled
  intro r
  by_cases hr : 0 < N.pre c r
  · by_cases e : r = q
    · subst e
      apply Classical.byContradiction
      intro hlt
      exact hno (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨c, hc, by omega⟩)))))
    · exact absurd (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨c, r, hc, hr, e⟩))))) hno
  · omega

/-! ## Soundness -/

section Soundness

variable {N cap}
variable {t0 : Fin T} {R : Fin T → Prop}

/-- The chosen place of a member. -/
noncomputable def place (closed : Closed N cap t0 R) (t : Fin T) (h : R t) : Fin P :=
  Classical.choose (closed t h)

noncomputable def val (closed : Closed N cap t0 R) (t : Fin T) (h : R t) : Nat :=
  Classical.choose (Classical.choose_spec (closed t h))

theorem spec (closed : Closed N cap t0 R) (t : Fin T) (h : R t) :
    Opt N cap t0 t (place closed t h) (val closed t h) ∧
      (Ends N t0 t (place closed t h) (val closed t h) ∨
        ∀ c, 0 < N.pre c (place closed t h) → R c) :=
  Classical.choose_spec (Classical.choose_spec (closed t h))

def EndsAt (closed : Closed N cap t0 R) (t : Fin T) (h : R t) : Prop :=
  Ends N t0 t (place closed t h) (val closed t h)

/-- One step of the chain: a member that does not end passes to the consumer
of its chosen place. -/
def Step (closed : Closed N cap t0 R) (t u : Fin T) : Prop :=
  ∃ h : R t, ¬ EndsAt closed t h ∧ 0 < N.pre u (place closed t h)

inductive Visited (closed : Closed N cap t0 R) : Fin T → Prop
  | start : Visited closed t0
  | step {t u : Fin T} : Visited closed t → Step closed t u → Visited closed u

theorem visited_mem (h0 : R t0) (closed : Closed N cap t0 R) {t : Fin T}
    (v : Visited closed t) : R t := by
  induction v with
  | start => exact h0
  | step _ st _ =>
    obtain ⟨h, ne, hu⟩ := st
    rcases (spec closed _ h).2 with e | inR
    · exact absurd e ne
    · exact inR _ hu

theorem step_det (cf : IsConflictFree N) (closed : Closed N cap t0 R) {t u u' : Fin T}
    (s : Step closed t u) (s' : Step closed t u') : u = u' := by
  obtain ⟨_, _, hu⟩ := s
  obtain ⟨_, _, hu'⟩ := s'
  exact cf _ _ _ hu hu'

/-- Reachability along steps. -/
inductive Reach (closed : Closed N cap t0 R) : Fin T → Fin T → Prop
  | refl (t : Fin T) : Reach closed t t
  | step {t u w : Fin T} : Step closed t u → Reach closed u w → Reach closed t w

theorem reach_snoc (closed : Closed N cap t0 R) {t u w : Fin T} (r : Reach closed t u)
    (s : Step closed u w) : Reach closed t w := by
  induction r with
  | refl _ => exact Reach.step s (Reach.refl _)
  | step s1 _ ih => exact Reach.step s1 (ih s)

theorem reach_of_visited (closed : Closed N cap t0 R) {t : Fin T} (v : Visited closed t) :
    Reach closed t0 t := by
  induction v with
  | start => exact Reach.refl _
  | step _ s ih => exact reach_snoc closed ih s

/-- Visited transitions are linearly ordered by reachability. -/
theorem visited_linear (cf : IsConflictFree N) (closed : Closed N cap t0 R) {a b : Fin T}
    (va : Visited closed a) (vb : Visited closed b) :
    Reach closed a b ∨ Reach closed b a := by
  induction vb with
  | start => exact Or.inr (reach_of_visited closed va)
  | step _ s ih =>
    rcases ih with r | r
    · exact Or.inl (reach_snoc closed r s)
    · cases r with
      | refl => exact Or.inl (Reach.step s (Reach.refl _))
      | step s1 r1 =>
        have := step_det cf closed s s1
        subst this
        exact Or.inr r1

theorem reach_from_end (closed : Closed N cap t0 R) {e w : Fin T} (he : R e)
    (end_ : EndsAt closed e he) (r : Reach closed e w) : w = e := by
  cases r with
  | refl => rfl
  | step s _ =>
    obtain ⟨h, ne, _⟩ := s
    exact absurd end_ ne

/-- **At most one visited member ends.** -/
theorem end_unique (cf : IsConflictFree N) (closed : Closed N cap t0 R) {e e' : Fin T}
    (v : Visited closed e) (v' : Visited closed e')
    (he : R e) (he' : R e') (E : EndsAt closed e he) (E' : EndsAt closed e' he') : e = e' := by
  rcases visited_linear cf closed v v' with r | r
  · exact (reach_from_end closed he E r).symm
  · exact reach_from_end closed he' E' r

def ContSel (closed : Closed N cap t0 R) (q : Fin P) : Prop :=
  ∃ t, ∃ h : R t, Visited closed t ∧ ¬ EndsAt closed t h ∧ place closed t h = q

def EndSel (closed : Closed N cap t0 R) (q : Fin P) : Prop :=
  ∃ t, ∃ h : R t, Visited closed t ∧ EndsAt closed t h ∧ place closed t h = q

open Classical in
/-- The marking: continuing places full, the ending place at its value, `t0`'s
inputs at their floor, everything else empty. -/
noncomputable def mk (closed : Closed N cap t0 R) (q : Fin P) : Nat :=
  if ContSel closed q then cap q
  else if hE : EndSel closed q then
    val closed (Classical.choose hE) (Classical.choose (Classical.choose_spec hE))
  else N.pre t0 q

theorem mk_admissible (floor : ∀ q, N.pre t0 q ≤ cap q) (closed : Closed N cap t0 R) :
    Admissible cap (mk closed) := by
  intro q
  unfold mk
  split
  · exact Nat.le_refl _
  split
  · rename_i hE
    have hp := (Classical.choose_spec (Classical.choose_spec hE)).2.2
    have s := (spec closed (Classical.choose hE) (Classical.choose (Classical.choose_spec hE))).1.1
    rw [hp] at s
    exact s
  · exact floor q

/-- The value at an ending member's place is that member's value. -/
theorem mk_end (cf : IsConflictFree N) (closed : Closed N cap t0 R) {e : Fin T}
    (ve : Visited closed e) (he : R e) (E : EndsAt closed e he)
    (nc : ¬ ContSel closed (place closed e he)) :
    mk closed (place closed e he) = val closed e he := by
  have hE : EndSel closed (place closed e he) := ⟨e, he, ve, E, rfl⟩
  unfold mk
  simp only [nc, ite_false, hE, dite_true]
  have s := Classical.choose_spec hE
  obtain ⟨v', E', _⟩ := Classical.choose_spec s
  have eq := end_unique cf closed v' ve _ he E' E
  have key : ∀ (x : Fin T) (hx : R x), x = e → val closed x hx = val closed e he := by
    intro x hx h; subst h; rfl
  exact key _ _ eq

theorem mk_ge_val (cf : IsConflictFree N) (closed : Closed N cap t0 R) {t : Fin T}
    (vt : Visited closed t) (ht : R t) :
    val closed t ht ≤ mk closed (place closed t ht) := by
  by_cases nc : ContSel closed (place closed t ht)
  · unfold mk; simp only [nc, ite_true]; exact (spec closed t ht).1.1
  · by_cases E : EndsAt closed t ht
    · rw [mk_end cf closed vt ht E nc]
      exact Nat.le_refl _
    · exact absurd ⟨t, ht, vt, E, rfl⟩ nc

theorem t0_enabled (floor : ∀ q, N.pre t0 q ≤ cap q) (closed : Closed N cap t0 R) :
    OrdEnabled N (mk closed) t0 := by
  intro q
  unfold mk
  split
  · exact floor q
  split
  · rename_i hE
    have hp := (Classical.choose_spec (Classical.choose_spec hE)).2.2
    have s := (spec closed (Classical.choose hE) (Classical.choose (Classical.choose_spec hE))).1.2.1
    rw [hp] at s
    exact s
  · exact Nat.le_refl _

theorem visited_blocked (cf : IsConflictFree N) (h0 : R t0) (closed : Closed N cap t0 R)
    {t : Fin T} (vt : Visited closed t) : ¬ CapEnabled N cap (mk closed) t := by
  intro ⟨_, fits⟩
  have ht := visited_mem h0 closed vt
  have ov := (spec closed t ht).1.2.2
  have ge := mk_ge_val cf closed vt ht
  have := fits (place closed t ht)
  omega

theorem unvisited_blocked (cf : IsConflictFree N) (hin : HasInput N)
    (closed : Closed N cap t0 R) {u : Fin T} (nv : ¬ Visited closed u) :
    ¬ OrdEnabled N (mk closed) u := by
  intro ord
  have raised : ∀ r, 0 < N.pre u r → ¬ ContSel closed r ∧ EndSel closed r := by
    intro r hr
    have hm := ord r
    have nc : ¬ ContSel closed r := fun ⟨t, ht, vt, ne, hp⟩ =>
      nv (Visited.step vt ⟨ht, ne, hp ▸ hr⟩)
    refine ⟨nc, ?_⟩
    apply Classical.byContradiction
    intro nE
    unfold mk at hm
    simp only [nc, ite_false, nE, dite_false] at hm
    have : u = t0 := cf r u t0 hr (by omega)
    exact nv (by rw [this]; exact Visited.start)
  obtain ⟨r, hr⟩ := hin u
  obtain ⟨nc, ⟨e, he, ve, E, hp⟩⟩ := raised r hr
  subst hp
  have hm := ord (place closed e he)
  rw [mk_end cf closed ve he E nc] at hm
  have E0 := E
  rcases E0 with none | self | ofT0 | ⟨c, r', hc, hr', ne⟩ | ⟨c, hc, lt⟩
  · have := none u; omega
  · have : u = e := cf _ u e hr self
    exact nv (by rw [this]; exact ve)
  · have : u = t0 := cf _ u t0 hr ofT0
    exact nv (by rw [this]; exact Visited.start)
  · have : c = u := cf _ c u hc hr
    subst this
    obtain ⟨_, ⟨e', he', ve', E', hp'⟩⟩ := raised r' hr'
    have := end_unique cf closed ve' ve he' he E' E
    subst this
    exact ne hp'.symm
  · have : c = u := cf _ c u hc hr
    subst this
    omega

theorem bad_of_certificate (cf : IsConflictFree N) (hin : HasInput N)
    (floor : ∀ q, N.pre t0 q ≤ cap q) (h0 : R t0) (closed : Closed N cap t0 R) :
    ∃ m, Admissible cap m ∧ CapDead N cap m ∧ ∃ t, OrdEnabled N m t := by
  refine ⟨mk closed, mk_admissible floor closed, ?_, t0, t0_enabled floor closed⟩
  intro t
  by_cases vt : Visited closed t
  · exact visited_blocked cf h0 closed vt
  · exact fun en => unvisited_blocked cf hin closed vt en.1

end Soundness

/-- **The characterization.**  For a conflict-free net in which every transition
has an input place, the capacity invents a deadlock exactly when a chain
certificate exists. -/
theorem not_preserves_iff_certificate (cf : IsConflictFree N) (hin : HasInput N) :
    ¬ Preserves N cap ↔ Certificate N cap := by
  rw [not_preserves_iff_bad]
  constructor
  · intro ⟨m, adm, dead, t0, ord0⟩
    exact certificate_of_bad N cap adm dead ord0
  · intro ⟨t0, R, floor, h0, closed⟩
    exact bad_of_certificate cf hin floor h0 closed

end ConflictFree

end CBMDPetriCapacity
