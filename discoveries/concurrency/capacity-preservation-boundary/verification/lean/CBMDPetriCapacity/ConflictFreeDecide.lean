import CBMDPetriCapacity.ConflictFree

/-!
# A verified decision procedure for conflict-free nets

`ConflictFree.lean` proves `¬ Preserves ↔ Certificate` for conflict-free nets in
which every transition has an input place.  `Certificate` asks for *some*
post-fixpoint containing `t0`.  This module computes the greatest one by
iteration from the full set, proves that `T` rounds suffice (each round that
changes the set removes a transition), and so obtains an executable Boolean
`decidePreserves` with

    Preserves N cap  ↔  decidePreserves N cap = true.

This is the step revision 0.13.0 left to a census bridge.
-/

namespace CBMDPetriCapacity

namespace ConflictFree

variable {P T : Nat} (N : Net P T) (cap : Fin P → Nat)

/-- One round of the fixpoint: `t` survives if it has an option that ends or
whose consumer survived the previous round.  Values range over `Fin (cap q + 1)`,
so the quantifiers are finite. -/
def StepP (t0 : Fin T) (X : Fin T → Bool) (t : Fin T) : Prop :=
  ∃ q : Fin P, ∃ v : Fin (cap q + 1), Opt N cap t0 t q v.val ∧
    (Ends N t0 t q v.val ∨ ∀ c, 0 < N.pre c q → X c = true)

instance (t0 : Fin T) (X : Fin T → Bool) (t : Fin T) : Decidable (StepP N cap t0 X t) := by
  unfold StepP Opt Ends; exact inferInstance

def round (t0 : Fin T) (X : Fin T → Bool) : Fin T → Bool :=
  fun t => X t && decide (StepP N cap t0 X t)

def iter (t0 : Fin T) : Nat → Fin T → Bool
  | 0 => fun _ => true
  | k + 1 => round N cap t0 (iter t0 k)

def alive (t0 : Fin T) : Fin T → Bool := iter N cap t0 T

def count (X : Fin T → Bool) : Nat := (List.finRange T).countP (fun t => X t)

theorem round_le (t0 : Fin T) (X : Fin T → Bool) (t : Fin T) :
    round N cap t0 X t = true → X t = true := by
  simp only [round, Bool.and_eq_true]; exact fun h => h.1

theorem step_mono (t0 : Fin T) {X Y : Fin T → Bool} (le : ∀ t, X t = true → Y t = true)
    {t : Fin T} : StepP N cap t0 X t → StepP N cap t0 Y t := by
  intro ⟨q, v, o, e⟩
  exact ⟨q, v, o, e.imp id (fun h c hc => le c (h c hc))⟩

theorem countP_lt {α : Type} (p q : α → Bool) :
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
    · have ih := countP_lt p q l imp ⟨y, hl, hq, hp⟩
      cases hb : p a
      · cases q a <;> simp <;> omega
      · simp [imp a hb]; omega

theorem count_le (X : Fin T → Bool) : count X ≤ T := by
  unfold count
  have := @List.countP_le_length _ (fun t => X t) (List.finRange T)
  rw [List.length_finRange] at this
  exact this

/-- A round that changes the set strictly lowers its count. -/
theorem count_drop (t0 : Fin T) (X : Fin T → Bool) (ne : round N cap t0 X ≠ X) :
    count (round N cap t0 X) < count X := by
  apply countP_lt
  · exact fun z h => round_le N cap t0 X z h
  · apply Classical.byContradiction
    intro h
    apply ne
    funext t
    cases hr : round N cap t0 X t <;> cases hx : X t
    · rfl
    · exact absurd ⟨t, List.mem_finRange t, hx, hr⟩ h
    · exact absurd (round_le N cap t0 X t hr) (by simp [hx])
    · rfl

/-- After `k` rounds, either the set is already a fixpoint or at least `k`
transitions have been removed. -/
theorem fix_or_count (t0 : Fin T) :
    ∀ k, round N cap t0 (iter N cap t0 k) = iter N cap t0 k ∨
      count (iter N cap t0 k) + k ≤ T
  | 0 => Or.inr (by simp only [Nat.add_zero]; exact count_le _)
  | k + 1 => by
    rcases fix_or_count t0 k with fx | c
    · left
      show round N cap t0 (round N cap t0 (iter N cap t0 k)) = round N cap t0 (iter N cap t0 k)
      rw [fx, fx]
    · by_cases fx : round N cap t0 (iter N cap t0 k) = iter N cap t0 k
      · left
        show round N cap t0 (round N cap t0 (iter N cap t0 k)) = round N cap t0 (iter N cap t0 k)
        rw [fx, fx]
      · right
        have := count_drop N cap t0 _ fx
        show count (round N cap t0 (iter N cap t0 k)) + (k + 1) ≤ T
        omega

theorem alive_fix (t0 : Fin T) : round N cap t0 (alive N cap t0) = alive N cap t0 := by
  rcases fix_or_count N cap t0 T with fx | c
  · exact fx
  · -- every transition removed: the empty set is a fixpoint
    have zero : count (alive N cap t0) = 0 := by unfold alive; omega
    have empty : ∀ t, alive N cap t0 t = false := by
      intro t
      cases h : alive N cap t0 t
      · rfl
      · have : 0 < count (alive N cap t0) := by
          unfold count
          exact List.countP_pos_iff.mpr ⟨t, List.mem_finRange t, h⟩
        omega
    funext t
    cases h : round N cap t0 (alive N cap t0) t
    · exact (empty t).symm
    · exact absurd (round_le N cap t0 _ t h) (by simp [empty t])

/-- Every certificate set lies inside the computed one. -/
theorem closed_sub_iter (t0 : Fin T) {R : Fin T → Prop} (closed : Closed N cap t0 R) :
    ∀ k t, R t → iter N cap t0 k t = true
  | 0, _, _ => rfl
  | k + 1, t, ht => by
    show round N cap t0 (iter N cap t0 k) t = true
    simp only [round, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨closed_sub_iter t0 closed k t ht, ?_⟩
    obtain ⟨q, v, o, e⟩ := closed t ht
    exact ⟨q, ⟨v, by have := o.1; omega⟩, o,
      e.imp id (fun h c hc => closed_sub_iter t0 closed k c (h c hc))⟩

/-- The computed set is itself a certificate set. -/
theorem alive_closed (t0 : Fin T) : Closed N cap t0 (fun t => alive N cap t0 t = true) := by
  intro t ht
  have h := ht
  rw [← alive_fix N cap t0] at h
  simp only [round, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨q, v, o, e⟩ := h.2
  exact ⟨q, v.val, o, e⟩

theorem certificate_iff_alive :
    Certificate N cap ↔ ∃ t0, (∀ q, N.pre t0 q ≤ cap q) ∧ alive N cap t0 t0 = true := by
  constructor
  · intro ⟨t0, R, floor, h0, closed⟩
    exact ⟨t0, floor, closed_sub_iter N cap t0 closed T t0 h0⟩
  · intro ⟨t0, floor, h⟩
    exact ⟨t0, _, floor, h, alive_closed N cap t0⟩

/-- **The decision procedure.** -/
def decidePreserves : Bool :=
  (List.finRange T).all (fun t0 => !(decide (∀ q, N.pre t0 q ≤ cap q) && alive N cap t0 t0))

theorem preserves_iff_decide (cf : IsConflictFree N) (hin : HasInput N) :
    Preserves N cap ↔ decidePreserves N cap = true := by
  have key := (not_preserves_iff_certificate N cap cf hin).trans (certificate_iff_alive N cap)
  constructor
  · intro pres
    simp only [decidePreserves, List.all_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    intro t0 _
    apply Classical.byContradiction
    intro h
    simp only [not_or, Classical.not_not, Bool.not_eq_false] at h
    exact (key.mpr ⟨t0, h.1, h.2⟩) pres
  · intro d
    apply Classical.byContradiction
    intro np
    obtain ⟨t0, floor, h⟩ := key.mp np
    simp only [decidePreserves, List.all_eq_true] at d
    have := d t0 (List.mem_finRange t0)
    simp [floor, h] at this


/-! ## Only the threshold value matters

The decider above enumerates every value up to `cap q`, which is
pseudo-polynomial.  The smallest value at which `t` overflows at `q` and that
respects `t0`'s floor is always at least as good: overflow is monotone in the
value, and the only value-dependent ending reason (the consumer's lower
literal) prefers smaller values.  So one value per place suffices. -/

/-- The least value at which `t` overflows at `q`, raised to `t0`'s floor. -/
def thr (t0 t : Fin T) (q : Fin P) : Nat :=
  max (if cap q < N.post t q then 0 else N.pre t q + cap q + 1 - N.post t q) (N.pre t0 q)

theorem thr_overflow (t0 t : Fin T) (q : Fin P) :
    cap q < thr N cap t0 t q - N.pre t q + N.post t q := by
  unfold thr
  split <;> omega

theorem thr_le (t0 t : Fin T) (q : Fin P) {v : Nat} (o : Opt N cap t0 t q v) :
    thr N cap t0 t q ≤ v := by
  obtain ⟨_, fl, ov⟩ := o
  unfold thr
  split <;> omega

def StepT (t0 : Fin T) (X : Fin T → Bool) (t : Fin T) : Prop :=
  ∃ q : Fin P, thr N cap t0 t q ≤ cap q ∧
    (Ends N t0 t q (thr N cap t0 t q) ∨ ∀ c, 0 < N.pre c q → X c = true)

instance (t0 : Fin T) (X : Fin T → Bool) (t : Fin T) : Decidable (StepT N cap t0 X t) := by
  unfold StepT Ends; exact inferInstance

theorem stepP_iff_stepT (t0 : Fin T) (X : Fin T → Bool) (t : Fin T) :
    StepP N cap t0 X t ↔ StepT N cap t0 X t := by
  constructor
  · intro ⟨q, v, o, e⟩
    have hle := thr_le N cap t0 t q o
    refine ⟨q, Nat.le_trans hle o.1, ?_⟩
    rcases e with e | e
    · left
      rcases e with a | a | a | a | ⟨c, hc, lt⟩
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr (Or.inl a))
      · exact Or.inr (Or.inr (Or.inr (Or.inl a)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c, hc, by omega⟩)))
    · exact Or.inr e
  · intro ⟨q, hc, e⟩
    exact ⟨q, ⟨thr N cap t0 t q, by omega⟩, ⟨hc, Nat.le_max_right _ _, thr_overflow N cap t0 t q⟩, e⟩

def roundT (t0 : Fin T) (X : Fin T → Bool) : Fin T → Bool :=
  fun t => X t && decide (StepT N cap t0 X t)

theorem roundT_eq (t0 : Fin T) (X : Fin T → Bool) : roundT N cap t0 X = round N cap t0 X := by
  funext t
  simp only [roundT, round]
  congr 1
  exact decide_eq_decide.mpr (stepP_iff_stepT N cap t0 X t).symm

def iterT (t0 : Fin T) : Nat → Fin T → Bool
  | 0 => fun _ => true
  | k + 1 => roundT N cap t0 (iterT t0 k)

theorem iterT_eq (t0 : Fin T) : ∀ k, iterT N cap t0 k = iter N cap t0 k
  | 0 => rfl
  | k + 1 => by
    show roundT N cap t0 (iterT N cap t0 k) = round N cap t0 (iter N cap t0 k)
    rw [iterT_eq t0 k, roundT_eq]

/-- **The polynomial decider**: one candidate value per place. -/
def decidePreservesFast : Bool :=
  (List.finRange T).all (fun t0 => !(decide (∀ q, N.pre t0 q ≤ cap q) && iterT N cap t0 T t0))

theorem decideFast_eq : decidePreservesFast N cap = decidePreserves N cap := by
  unfold decidePreservesFast decidePreserves alive
  congr 1
  funext t0
  rw [iterT_eq]

theorem preserves_iff_decideFast (cf : IsConflictFree N) (hin : HasInput N) :
    Preserves N cap ↔ decidePreservesFast N cap = true := by
  rw [decideFast_eq]; exact preserves_iff_decide N cap cf hin

end ConflictFree

end CBMDPetriCapacity
