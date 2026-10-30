import CBMDPetriCapacity.Reduction

/-!
# The guard: arbitrary satisfiability into the restricted question

`Reduction.lean` shows the net preserves exactly when its CNF has no model
that is not all-false.  This module compiles the other half of revision
0.4.0's chain: an arbitrary CNF `G` on `n` atoms is satisfiable exactly when
its **guarded** form has a model that is not all-false.

Guarded atoms `Fin (n+n+1)`: `x_i` at `i`, `x̄_i` at `n+i`, the guard `g` at
`n+n`.  Guarded clauses `Fin (n+n+n+n+K)`, in five families:

| index | clause | negative literals |
|---|---|---|
| `i`        | `¬x_i ∨ ¬x̄_i`        | 2 |
| `n+i`      | `x_i ∨ x̄_i ∨ ¬g`     | 1 |
| `2n+i`     | `¬x_i ∨ g`           | 1 |
| `3n+i`     | `¬x̄_i ∨ g`           | 1 |
| `4n+c`     | clause `c` of `G` with `¬x_a` rewritten `x̄_a`, `∨ ¬g` | 1 |

So every transition of the resulting net has one or two input places, and
`NoTautology` holds.  Composed with `preserves_iff_no_nonzero_model`:

    Preserves (net (guard G)) cap  ↔  G is unsatisfiable.
-/

namespace CBMDPetriCapacity

namespace Reduction

variable {n K : Nat}

def gneg (_G : CNF n K) (c : Fin (n + n + n + n + K)) (a : Fin (n + n + 1)) : Bool :=
  if c.val < n then decide (a.val = c.val) || decide (a.val = n + c.val)
  else if c.val < n + n then decide (a.val = n + n)
  else if c.val < n + n + n then decide (a.val = c.val - (n + n))
  else if c.val < n + n + n + n then decide (a.val = n + (c.val - (n + n + n)))
  else decide (a.val = n + n)

def gpos (G : CNF n K) (c : Fin (n + n + n + n + K)) (a : Fin (n + n + 1)) : Bool :=
  if c.val < n then false
  else if c.val < n + n then decide (a.val = c.val - n) || decide (a.val = n + (c.val - n))
  else if c.val < n + n + n + n then decide (a.val = n + n)
  else if hc : c.val - (n + n + n + n) < K then
    if ha : a.val < n then G.pos ⟨c.val - (n + n + n + n), hc⟩ ⟨a.val, ha⟩
    else if ha' : a.val < n + n then G.neg ⟨c.val - (n + n + n + n), hc⟩ ⟨a.val - n, by omega⟩
    else false
  else false

def guard (G : CNF n K) : CNF (n + n + 1) (n + n + n + n + K) := ⟨gneg G, gpos G⟩

theorem guard_noTautology (G : CNF n K) : NoTautology (guard G) := by
  intro c a ⟨hn, hp⟩
  simp only [guard, gneg, gpos] at hn hp
  by_cases h1 : c.val < n
  · simp [h1] at hp
  by_cases h2 : c.val < n + n
  · simp [h1, h2] at hn hp; omega
  by_cases h3 : c.val < n + n + n
  · have h4 : c.val < n + n + n + n := by omega
    simp [h1, h2, h3, h4] at hn hp; omega
  by_cases h4 : c.val < n + n + n + n
  · simp [h1, h2, h3, h4] at hn hp; omega
  · simp only [h1, h2, h3, h4, ite_false, decide_eq_true_eq] at hn
    have a1 : ¬ a.val < n := by omega
    have a2 : ¬ a.val < n + n := by omega
    simp [h1, h2, h4, a1, a2] at hp

/-- Satisfiable in the ordinary sense. -/
def Satisfiable (G : CNF n K) : Prop := ∃ σ : Fin n → Bool, ∀ c, Satisfies G σ c

/-- The assignment on guarded atoms induced by one on `G`'s atoms. -/
def lift (σ : Fin n → Bool) (a : Fin (n + n + 1)) : Bool :=
  if h : a.val < n then σ ⟨a.val, h⟩
  else if h' : a.val < n + n then !σ ⟨a.val - n, by omega⟩
  else true

theorem lift_x (σ : Fin n → Bool) (i : Nat) (hi : i < n) :
    lift σ ⟨i, by omega⟩ = σ ⟨i, hi⟩ := by
  simp [lift, hi]

theorem lift_xb (σ : Fin n → Bool) (i : Nat) (hi : i < n) :
    lift σ ⟨n + i, by omega⟩ = !σ ⟨i, hi⟩ := by
  have a1 : ¬ n + i < n := by omega
  have a2 : n + i < n + n := by omega
  have e : n + i - n = i := by omega
  simp only [lift, a1, a2, dite_false, dite_true]
  congr 2
  exact Fin.ext e

theorem lift_g (σ : Fin n → Bool) : lift σ ⟨n + n, by omega⟩ = true := by
  have a1 : ¬ n + n < n + n := by omega
  have a0 : ¬ n + n < n := by omega
  simp [lift, a0, a1]

theorem satisfiable_to_nonzero (G : CNF n K) (h : Satisfiable G) : NonzeroModel (guard G) := by
  obtain ⟨σ, sat⟩ := h
  refine ⟨lift σ, fun c => ?_, ⟨⟨n + n, by omega⟩, lift_g σ⟩⟩
  simp only [Satisfies, guard]
  by_cases h1 : c.val < n
  · cases hs : σ ⟨c.val, h1⟩
    · exact ⟨⟨c.val, by omega⟩, Or.inl ⟨by simp [gneg, h1], by rw [lift_x σ _ h1, hs]⟩⟩
    · exact ⟨⟨n + c.val, by omega⟩, Or.inl ⟨by simp [gneg, h1], by rw [lift_xb σ _ h1, hs]; rfl⟩⟩
  by_cases h2 : c.val < n + n
  · have hi : c.val - n < n := by omega
    cases hs : σ ⟨c.val - n, hi⟩
    · exact ⟨⟨n + (c.val - n), by omega⟩, Or.inr ⟨by simp [gpos, h1, h2],
        by rw [lift_xb σ _ hi, hs]; rfl⟩⟩
    · exact ⟨⟨c.val - n, by omega⟩, Or.inr ⟨by simp [gpos, h1, h2], by rw [lift_x σ _ hi, hs]⟩⟩
  by_cases h4 : c.val < n + n + n + n
  · exact ⟨⟨n + n, by omega⟩, Or.inr ⟨by simp [gpos, h1, h2, h4], lift_g σ⟩⟩
  · have hc : c.val - (n + n + n + n) < K := by omega
    obtain ⟨a, ha⟩ := sat ⟨c.val - (n + n + n + n), hc⟩
    rcases ha with ⟨hn, hs⟩ | ⟨hp, hs⟩
    · refine ⟨⟨n + a.val, by omega⟩, Or.inr ⟨?_, by rw [lift_xb σ _ a.isLt, hs]; rfl⟩⟩
      have e1 : ¬ n + a.val < n := by omega
      have e2 : n + a.val < n + n := by omega
      have e : (⟨n + a.val - n, by omega⟩ : Fin n) = a := Fin.ext (by simp)
      simp only [gpos, h1, h2, h4, hc, e1, e2, ite_false, dite_true, dite_false, e, hn]
    · refine ⟨⟨a.val, by omega⟩, Or.inr ⟨?_, by rw [lift_x σ _ a.isLt, hs]⟩⟩
      simp only [gpos, h1, h2, h4, hc, a.isLt, ite_false, dite_true, hp]

theorem nonzero_to_satisfiable (G : CNF n K) (h : NonzeroModel (guard G)) : Satisfiable G := by
  obtain ⟨τ, sat, ⟨b, hb⟩⟩ := h
  have tf : ∀ {x : Bool}, x = true → x = false → False := by
    intro x h1 h2; rw [h1] at h2; exact Bool.noConfusion h2
  -- family 1: not both x_i and x̄_i
  have fam1 : ∀ i : Fin n, τ ⟨i.val, by omega⟩ = false ∨ τ ⟨n + i.val, by omega⟩ = false := by
    intro i
    obtain ⟨a, ha⟩ := sat ⟨i.val, by omega⟩
    simp only [guard, gneg, gpos, i.isLt, ite_true, decide_eq_true_eq, Bool.or_eq_true,
      Bool.false_eq_true, false_and, or_false] at ha
    obtain ⟨hn, hs⟩ := ha
    rcases hn with e | e
    · left
      have : (⟨i.val, by omega⟩ : Fin (n + n + 1)) = a := Fin.ext e.symm
      rw [this]; exact hs
    · right
      have : (⟨n + i.val, by omega⟩ : Fin (n + n + 1)) = a := Fin.ext e.symm
      rw [this]; exact hs
  have gtrue : τ ⟨n + n, by omega⟩ = true := by
    cases hg : τ ⟨n + n, by omega⟩
    · exfalso
      have xs : ∀ i : Fin n, τ ⟨i.val, by omega⟩ = false := by
        intro i
        obtain ⟨a, ha⟩ := sat ⟨n + n + i.val, by omega⟩
        have c1 : ¬ n + n + i.val < n := by omega
        have c2 : ¬ n + n + i.val < n + n := by omega
        have c3 : n + n + i.val < n + n + n := by omega
        have c4 : n + n + i.val < n + n + n + n := by omega
        simp only [guard, gneg, gpos, c1, c2, c3, c4, ite_true, ite_false,
          decide_eq_true_eq] at ha
        rcases ha with ⟨hn, hs⟩ | ⟨hp, hs⟩
        · have : (⟨i.val, by omega⟩ : Fin (n + n + 1)) = a := Fin.ext (by show i.val = a.val; omega)
          rw [this]; exact hs
        · have : (⟨n + n, by omega⟩ : Fin (n + n + 1)) = a := Fin.ext hp.symm
          rw [← this] at hs; exact (tf hs hg).elim
      have xbs : ∀ i : Fin n, τ ⟨n + i.val, by omega⟩ = false := by
        intro i
        obtain ⟨a, ha⟩ := sat ⟨n + n + n + i.val, by omega⟩
        have c1 : ¬ n + n + n + i.val < n := by omega
        have c2 : ¬ n + n + n + i.val < n + n := by omega
        have c3 : ¬ n + n + n + i.val < n + n + n := by omega
        have c4 : n + n + n + i.val < n + n + n + n := by omega
        simp only [guard, gneg, gpos, c1, c2, c3, c4, ite_true, ite_false,
          decide_eq_true_eq] at ha
        rcases ha with ⟨hn, hs⟩ | ⟨hp, hs⟩
        · have : (⟨n + i.val, by omega⟩ : Fin (n + n + 1)) = a :=
            Fin.ext (by show n + i.val = a.val; omega)
          rw [this]; exact hs
        · have : (⟨n + n, by omega⟩ : Fin (n + n + 1)) = a := Fin.ext hp.symm
          rw [← this] at hs; exact (tf hs hg).elim
      by_cases b1 : b.val < n
      · have h := xs ⟨b.val, b1⟩
        have e : (⟨b.val, by omega⟩ : Fin (n + n + 1)) = b := Fin.ext rfl
        rw [e] at h; exact tf hb h
      by_cases b2 : b.val < n + n
      · have h := xbs ⟨b.val - n, by omega⟩
        have e : (⟨n + (b.val - n), by omega⟩ : Fin (n + n + 1)) = b :=
          Fin.ext (by show n + (b.val - n) = b.val; omega)
        rw [e] at h; exact tf hb h
      · have e : (⟨n + n, by omega⟩ : Fin (n + n + 1)) = b :=
          Fin.ext (by show n + n = b.val; omega)
        rw [e] at hg; exact tf hb hg
    · rfl
  refine ⟨fun i => τ ⟨i.val, by omega⟩, fun c => ?_⟩
  obtain ⟨a, ha⟩ := sat ⟨n + n + n + n + c.val, by omega⟩
  have c1 : ¬ n + n + n + n + c.val < n := by omega
  have c2 : ¬ n + n + n + n + c.val < n + n := by omega
  have c3 : ¬ n + n + n + n + c.val < n + n + n := by omega
  have c4 : ¬ n + n + n + n + c.val < n + n + n + n := by omega
  have hc : n + n + n + n + c.val - (n + n + n + n) < K := by omega
  simp only [guard, gneg, gpos, c1, c2, c3, c4, ite_false, hc, dite_true,
    decide_eq_true_eq] at ha
  have ec : (⟨n + n + n + n + c.val - (n + n + n + n), hc⟩ : Fin K) = c :=
    Fin.ext (by show n + n + n + n + c.val - (n + n + n + n) = c.val; omega)
  rw [ec] at ha
  rcases ha with ⟨hn, hs⟩ | ⟨hp, hs⟩
  · have : (⟨n + n, by omega⟩ : Fin (n + n + 1)) = a := Fin.ext hn.symm
    rw [← this] at hs; exact (tf gtrue hs).elim
  · by_cases a1 : a.val < n
    · simp only [a1, dite_true] at hp
      exact ⟨⟨a.val, a1⟩, Or.inr ⟨hp, hs⟩⟩
    · by_cases a2 : a.val < n + n
      · simp only [a1, a2, dite_true, dite_false] at hp
        refine ⟨⟨a.val - n, by omega⟩, Or.inl ⟨hp, ?_⟩⟩
        have ea : (⟨n + (a.val - n), by omega⟩ : Fin (n + n + 1)) = a :=
          Fin.ext (by show n + (a.val - n) = a.val; omega)
        rcases fam1 ⟨a.val - n, by omega⟩ with h | h
        · exact h
        · rw [ea] at h; exact (tf hs h).elim
      · simp [a1, a2] at hp

/-- **The guard.**  `G` is satisfiable exactly when its guarded form has a model
that is not all-false. -/
theorem satisfiable_iff_guard_nonzero (G : CNF n K) :
    Satisfiable G ↔ NonzeroModel (guard G) :=
  ⟨satisfiable_to_nonzero G, nonzero_to_satisfiable G⟩

/-- **The full reduction.**  The net built from the guarded form of an
arbitrary CNF preserves exactly when the CNF is unsatisfiable. -/
theorem preserves_iff_unsatisfiable (G : CNF n K) :
    Preserves (net (guard G)) cap ↔ ¬ Satisfiable G := by
  rw [preserves_iff_no_nonzero_model _ (guard_noTautology G), satisfiable_iff_guard_nonzero]

/-- Every guarded clause has at least one and at most two negative literals —
the input-place count of revision 0.4.0's dichotomy. -/
theorem guard_neg_count (G : CNF n K) (c : Fin (n + n + n + n + K)) :
    (∃ a, (guard G).neg c a = true) ∧
      ∀ a b d, (guard G).neg c a = true → (guard G).neg c b = true →
        (guard G).neg c d = true → a = b ∨ a = d ∨ b = d := by
  constructor
  · simp only [guard, gneg]
    split
    · exact ⟨⟨c.val, by omega⟩, by simp⟩
    split
    · exact ⟨⟨n + n, by omega⟩, by simp⟩
    split
    · exact ⟨⟨c.val - (n + n), by omega⟩, by simp⟩
    split
    · exact ⟨⟨n + (c.val - (n + n + n)), by omega⟩, by simp⟩
    · exact ⟨⟨n + n, by omega⟩, by simp⟩
  · have key : ∃ u w : Nat, ∀ a, (guard G).neg c a = true → a.val = u ∨ a.val = w := by
      simp only [guard, gneg]
      split
      · exact ⟨c.val, n + c.val, fun a h => by simpa using h⟩
      split
      · exact ⟨n + n, n + n, fun a h => by simp at h; omega⟩
      split
      · exact ⟨c.val - (n + n), c.val - (n + n), fun a h => by simp at h; omega⟩
      split
      · exact ⟨n + (c.val - (n + n + n)), n + (c.val - (n + n + n)),
          fun a h => by simp at h; omega⟩
      · exact ⟨n + n, n + n, fun a h => by simp at h; omega⟩
    obtain ⟨u, w, hk⟩ := key
    intro a b d ha hb hd
    have := hk a ha; have := hk b hb; have := hk d hd
    by_cases e1 : a.val = b.val
    · exact Or.inl (Fin.ext e1)
    by_cases e2 : a.val = d.val
    · exact Or.inr (Or.inl (Fin.ext e2))
    · exact Or.inr (Or.inr (Fin.ext (by omega)))

end Reduction

end CBMDPetriCapacity
