import CBMDWeightedDynamics.Iff

/-!
# A verified decider for the weighted characterization

`terminalStable_iff` characterizes terminal stability by well-foundedness of
`LiveArc`, live-closure and the bound.  The last two are finite checks.  This
module decides the first by peeling: start from all vertices and repeatedly
keep only live vertices with a live out-neighbour still kept.  The surviving
set is empty exactly when `LiveArc` is well founded, and `n` rounds suffice.
The result is an executable Boolean `decideTerminalStable` with

    TerminalStable mult outdegree capacity ↔ decideTerminalStable .. = true.
-/

namespace CBMDWeightedDynamics

variable {n : Nat} (mult : Vertex n → Vertex n → Nat) (outdegree capacity : Vertex n → Nat)

instance : DecidablePred (Live outdegree capacity) := fun v => by
  unfold Live; exact inferInstance

def peel (X : Vertex n → Bool) : Vertex n → Bool :=
  fun v => X v && decide (Live outdegree capacity v ∧
    ∃ w, X w = true ∧ Live outdegree capacity w ∧ 0 < mult v w)

def peelIter : Nat → Vertex n → Bool
  | 0 => fun _ => true
  | k + 1 => peel mult outdegree capacity (peelIter k)

def vcount (X : Vertex n → Bool) : Nat := (List.finRange n).countP (fun v => X v)

theorem peel_le (X : Vertex n → Bool) (v : Vertex n) :
    peel mult outdegree capacity X v = true → X v = true := by
  simp only [peel, Bool.and_eq_true]; exact fun h => h.1

theorem countP_lt' {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ z, p z = true → q z = true) →
      (∃ y, y ∈ l ∧ q y = true ∧ p y = false) → l.countP p < l.countP q
  | [], _, ⟨_, hy, _⟩ => absurd hy List.not_mem_nil
  | a :: l, imp, ⟨y, hy, hq, hp⟩ => by
    have mono : ∀ (l : List α), l.countP p ≤ l.countP q := by
      intro l
      induction l with
      | nil => simp
      | cons b l ih =>
        simp only [List.countP_cons]
        cases hb : p b
        · cases q b <;> simp <;> omega
        · simp [imp b hb]; omega
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hy with rfl | hl
    · simp [hq, hp]
      have := mono l
      omega
    · have ih := countP_lt' p q l imp ⟨y, hl, hq, hp⟩
      cases hb : p a
      · cases q a <;> simp <;> omega
      · simp [imp a hb]; omega

theorem vcount_le (X : Vertex n → Bool) : vcount X ≤ n := by
  unfold vcount
  have := @List.countP_le_length _ (fun v => X v) (List.finRange n)
  rw [List.length_finRange] at this
  exact this

theorem peel_drop (X : Vertex n → Bool) (ne : peel mult outdegree capacity X ≠ X) :
    vcount (peel mult outdegree capacity X) < vcount X := by
  apply countP_lt'
  · exact fun z h => peel_le mult outdegree capacity X z h
  · apply Classical.byContradiction
    intro h
    apply ne
    funext v
    cases hr : peel mult outdegree capacity X v <;> cases hx : X v
    · rfl
    · exact absurd ⟨v, List.mem_finRange v, hx, hr⟩ h
    · exact absurd (peel_le mult outdegree capacity X v hr) (by simp [hx])
    · rfl

theorem peel_fix_or_count :
    ∀ k, peel mult outdegree capacity (peelIter mult outdegree capacity k) =
        peelIter mult outdegree capacity k ∨
      vcount (peelIter mult outdegree capacity k) + k ≤ n
  | 0 => Or.inr (by simp only [Nat.add_zero]; exact vcount_le _)
  | k + 1 => by
    rcases peel_fix_or_count k with fx | c
    · left
      show peel mult outdegree capacity (peel mult outdegree capacity (peelIter mult outdegree capacity k)) =
        peel mult outdegree capacity (peelIter mult outdegree capacity k)
      rw [fx, fx]
    · by_cases fx : peel mult outdegree capacity (peelIter mult outdegree capacity k) =
          peelIter mult outdegree capacity k
      · left
        show peel mult outdegree capacity (peel mult outdegree capacity (peelIter mult outdegree capacity k)) =
          peel mult outdegree capacity (peelIter mult outdegree capacity k)
        rw [fx, fx]
      · right
        have := peel_drop mult outdegree capacity _ fx
        show vcount (peel mult outdegree capacity (peelIter mult outdegree capacity k)) + (k + 1) ≤ n
        omega

/-- The core: what survives `n` rounds of peeling. -/
def core : Vertex n → Bool := peelIter mult outdegree capacity n

theorem core_fix : peel mult outdegree capacity (core mult outdegree capacity) =
    core mult outdegree capacity := by
  rcases peel_fix_or_count mult outdegree capacity n with fx | c
  · exact fx
  · have zero : vcount (core mult outdegree capacity) = 0 := by unfold core; omega
    have empty : ∀ v, core mult outdegree capacity v = false := by
      intro v
      cases h : core mult outdegree capacity v
      · rfl
      · have : 0 < vcount (core mult outdegree capacity) := by
          unfold vcount
          exact List.countP_pos_iff.mpr ⟨v, List.mem_finRange v, h⟩
        omega
    funext v
    cases h : peel mult outdegree capacity (core mult outdegree capacity) v
    · exact (empty v).symm
    · exact absurd (peel_le mult outdegree capacity _ v h) (by simp [empty v])

/-- Members of the core are not accessible. -/
theorem core_not_acc : ∀ v, core mult outdegree capacity v = true →
    ¬ Acc (LiveArc mult outdegree capacity) v := by
  intro v hv acc
  induction acc with
  | intro v _ ih =>
    have h := hv
    rw [← core_fix mult outdegree capacity] at h
    simp only [peel, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨lv, w, hw, lw, arc⟩ := h.2
    exact ih w ⟨lv, lw, arc⟩ hw

/-- Non-accessible vertices survive every round. -/
theorem notAcc_in_iter : ∀ k v, ¬ Acc (LiveArc mult outdegree capacity) v →
    peelIter mult outdegree capacity k v = true
  | 0, _, _ => rfl
  | k + 1, v, na => by
    show peel mult outdegree capacity (peelIter mult outdegree capacity k) v = true
    simp only [peel, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨notAcc_in_iter k v na, ?_⟩
    have ⟨w, hw, nw⟩ : ∃ w, LiveArc mult outdegree capacity w v ∧
        ¬ Acc (LiveArc mult outdegree capacity) w :=
      Classical.byContradiction fun h => na (Acc.intro v fun w hw =>
        Classical.byContradiction fun nw => h ⟨w, hw, nw⟩)
    exact ⟨hw.1, w, notAcc_in_iter k w nw, hw.2.1, hw.2.2⟩

theorem wellFounded_iff_core_empty :
    WellFounded (LiveArc mult outdegree capacity) ↔ ∀ v, core mult outdegree capacity v = false := by
  constructor
  · intro wf v
    cases h : core mult outdegree capacity v
    · rfl
    · exact absurd (wf.apply v) (core_not_acc mult outdegree capacity v h)
  · intro empty
    refine ⟨fun v => Classical.byContradiction fun na => ?_⟩
    have := notAcc_in_iter mult outdegree capacity n v na
    rw [show peelIter mult outdegree capacity n v = core mult outdegree capacity v from rfl,
      empty v] at this
    exact Bool.noConfusion this

/-- **The decider.** -/
def decideTerminalStable : Bool :=
  decide (∀ v, core mult outdegree capacity v = false) &&
    decide (∀ u v, Live outdegree capacity u → 0 < mult u v → Live outdegree capacity v) &&
    decide (∀ u v, Live outdegree capacity u → Live outdegree capacity v →
      0 < mult u v → outdegree v + mult u v ≤ capacity v + 1)

theorem terminalStable_iff_decide (pos : ∀ u, 0 < outdegree u) :
    TerminalStable mult outdegree capacity ↔ decideTerminalStable mult outdegree capacity = true := by
  rw [terminalStable_iff mult outdegree capacity pos, wellFounded_iff_core_empty]
  simp only [decideTerminalStable, Bool.and_eq_true, decide_eq_true_eq, LiveClosed, LiveBound]
  exact ⟨fun ⟨a, b, c⟩ => ⟨⟨a, b⟩, c⟩, fun ⟨⟨a, b⟩, c⟩ => ⟨a, b, c⟩⟩

end CBMDWeightedDynamics
