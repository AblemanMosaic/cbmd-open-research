import CBMDPetriCapacity.Core

/-!
# The hardness reduction, compiled

Revision 0.4.0 proves `PRESERVES` coNP-complete at two input places by a
written argument, and machine-checks the reduction only by census
(`verification/hardness.py`).  This module compiles the reduction's
correctness: the net built from a CNF preserves exactly when the CNF has no
model that is not all-false.

The complexity-class statement itself is still not formalized — that needs a
model of computation — but the mathematical content of the reduction no
longer rests on a census.

## The encoding (as in `hardness.py`)

* places: one per atom, capacity `1`, and a last place `z` of capacity `0`;
* one transition per clause: input `1` on each negative literal's atom, output
  `1` on each positive literal's atom;
* one probe transition per atom: input `1` from the atom, output `1` into `z`.

**A hypothesis the census never states.** No clause may contain an atom with
both signs.  A clause `x ∨ ¬x` would give a transition that consumes and
produces at `x`, which is capacity-enabled when `x` holds a token although the
clause is satisfied.  `hardness.py` never produces such a clause: the guarded
encoding sends `x` and `¬x` to different atoms.  It is carried here as the
explicit hypothesis `NoTautology`.
-/

namespace CBMDPetriCapacity

namespace Reduction

/-- A CNF on `A` atoms with `K` clauses: `neg c a` / `pos c a` say that atom
`a` occurs negatively / positively in clause `c`. -/
structure CNF (A K : Nat) where
  neg : Fin K → Fin A → Bool
  pos : Fin K → Fin A → Bool

variable {A K : Nat}

def NoTautology (F : CNF A K) : Prop := ∀ c a, ¬ (F.neg c a = true ∧ F.pos c a = true)

def Satisfies (F : CNF A K) (σ : Fin A → Bool) (c : Fin K) : Prop :=
  ∃ a, (F.neg c a = true ∧ σ a = false) ∨ (F.pos c a = true ∧ σ a = true)

/-- The question the reduction answers: a model that is not all-false. -/
def NonzeroModel (F : CNF A K) : Prop :=
  ∃ σ : Fin A → Bool, (∀ c, Satisfies F σ c) ∧ ∃ a, σ a = true

def ind (b : Bool) : Nat := if b then 1 else 0

/-- The net.  Places `Fin (A+1)` (atoms, then `z`); transitions `Fin (K+A)`
(clauses, then probes). -/
def net (F : CNF A K) : Net (A + 1) (K + A) where
  pre := Fin.addCases
    (fun c q => Fin.lastCases 0 (fun a => ind (F.neg c a)) q)
    (fun b q => Fin.lastCases 0 (fun a => ind (decide (a = b))) q)
  post := Fin.addCases
    (fun c q => Fin.lastCases 0 (fun a => ind (F.pos c a)) q)
    (fun _ q => Fin.lastCases 1 (fun _ => 0) q)

def cap : Fin (A + 1) → Nat := fun q => Fin.lastCases 0 (fun _ => 1) q

/-- Read an assignment off a marking. -/
def assign (m : Marking (A + 1)) : Fin A → Bool := fun a => decide (0 < m a.castSucc)

/-- Write a marking from an assignment. -/
def mark (σ : Fin A → Bool) : Marking (A + 1) :=
  fun q => Fin.lastCases 0 (fun a => ind (σ a)) q

theorem mark_admissible (σ : Fin A → Bool) : Admissible cap (mark σ) := by
  intro q
  induction q using Fin.lastCases with
  | last => simp [mark, cap]
  | cast a => simp only [mark, cap, Fin.lastCases_castSucc, ind]; split <;> omega

theorem assign_mark (σ : Fin A → Bool) : assign (mark σ) = σ := by
  funext a
  simp only [assign, mark, Fin.lastCases_castSucc, ind]
  cases σ a <;> simp

/-- Probes never fire under the capacity: `z` has capacity `0`. -/
theorem probe_not_capEnabled (F : CNF A K) (m : Marking (A + 1)) (b : Fin A) :
    ¬ CapEnabled (net F) cap m (Fin.natAdd K b) := by
  intro ⟨_, fits⟩
  have := fits (Fin.last A)
  simp [net, cap, Fin.addCases_right, Fin.lastCases_last] at this

/-- A probe is ordinarily enabled exactly when its atom holds a token. -/
theorem probe_ordEnabled_of_pos (F : CNF A K) {m : Marking (A + 1)} {b : Fin A}
    (h : 0 < m b.castSucc) : OrdEnabled (net F) m (Fin.natAdd K b) := by
  intro q
  induction q using Fin.lastCases with
  | last => simp [net]
  | cast a =>
    simp only [net, Fin.addCases_right, Fin.lastCases_castSucc, ind]
    by_cases hab : a = b
    · subst hab; simp; omega
    · simp [hab]

theorem pos_of_probe_ordEnabled (F : CNF A K) {m : Marking (A + 1)} {b : Fin A}
    (h : OrdEnabled (net F) m (Fin.natAdd K b)) : 0 < m b.castSucc := by
  have := h b.castSucc
  simp [net, Fin.addCases_right, Fin.lastCases_castSucc, ind] at this
  omega

/-- On admissible markings, a clause transition is capacity-enabled exactly
when the clause is falsified by the read-off assignment. -/
theorem clause_capEnabled_iff (F : CNF A K) (nt : NoTautology F)
    {m : Marking (A + 1)} (adm : Admissible cap m) (c : Fin K) :
    CapEnabled (net F) cap m (Fin.castAdd A c) ↔ ¬ Satisfies F (assign m) c := by
  have atom_le : ∀ a : Fin A, m a.castSucc ≤ 1 := fun a => by
    have := adm a.castSucc; simpa [cap] using this
  constructor
  · intro ⟨ord, fits⟩ ⟨a, h⟩
    rcases h with ⟨hn, hs⟩ | ⟨hp, hs⟩
    · have := ord a.castSucc
      simp [net, Fin.addCases_left, Fin.lastCases_castSucc, ind, hn] at this
      simp [assign] at hs; omega
    · have := fits a.castSucc
      have hn : F.neg c a = false := by
        cases h' : F.neg c a
        · rfl
        · exact absurd ⟨h', hp⟩ (nt c a)
      simp [net, cap, Fin.addCases_left, Fin.lastCases_castSucc, ind, hn, hp] at this
      simp [assign] at hs; omega
  · intro unsat
    have each : ∀ a, (F.neg c a = true → assign m a = true) ∧
        (F.pos c a = true → assign m a = false) := by
      intro a
      constructor
      · intro hn
        cases hs : assign m a
        · exact absurd ⟨a, Or.inl ⟨hn, hs⟩⟩ unsat
        · rfl
      · intro hp
        cases hs : assign m a
        · rfl
        · exact absurd ⟨a, Or.inr ⟨hp, hs⟩⟩ unsat
    constructor
    · intro q
      induction q using Fin.lastCases with
      | last => simp [net]
      | cast a =>
        simp only [net, Fin.addCases_left, Fin.lastCases_castSucc, ind]
        cases hn : F.neg c a
        · simp
        · have := (each a).1 hn
          simp [assign] at this; simp; omega
    · intro q
      induction q using Fin.lastCases with
      | last =>
        have := adm (Fin.last A)
        simp [net, cap] at this ⊢; exact this
      | cast a =>
        simp only [net, cap, Fin.addCases_left, Fin.lastCases_castSucc, ind]
        have hle := atom_le a
        cases hp : F.pos c a
        · cases F.neg c a <;> simp <;> omega
        · have := (each a).2 hp
          simp [assign] at this
          cases F.neg c a <;> simp <;> omega

/-- **Reduction correctness.**  Under `NoTautology`, the net preserves exactly
when the CNF has no model that is not all-false. -/
theorem preserves_iff_no_nonzero_model (F : CNF A K) (nt : NoTautology F) :
    Preserves (net F) cap ↔ ¬ NonzeroModel F := by
  constructor
  · intro pres ⟨σ, sat, a, ha⟩
    have dead : CapDead (net F) cap (mark σ) := by
      intro t
      induction t using Fin.addCases with
      | left c =>
        rw [clause_capEnabled_iff F nt (mark_admissible σ), assign_mark]
        exact fun h => h (sat c)
      | right b => exact probe_not_capEnabled F _ b
    apply pres (mark σ) (mark_admissible σ) dead (Fin.natAdd K a)
    apply probe_ordEnabled_of_pos
    simp [mark, Fin.lastCases_castSucc, ind, ha]
  · intro none m adm dead t ord
    apply none
    refine ⟨assign m, fun c => ?_, ?_⟩
    · exact Classical.byContradiction fun h =>
        dead (Fin.castAdd A c) ((clause_capEnabled_iff F nt adm c).mpr h)
    · induction t using Fin.addCases with
      | right b => exact ⟨b, by simp [assign]; exact pos_of_probe_ordEnabled F ord⟩
      | left c =>
        have sat : Satisfies F (assign m) c := Classical.byContradiction fun h =>
          dead (Fin.castAdd A c) ((clause_capEnabled_iff F nt adm c).mpr h)
        obtain ⟨a, h⟩ := sat
        rcases h with ⟨hn, hs⟩ | ⟨_, hs⟩
        · have := ord a.castSucc
          simp [net, Fin.addCases_left, Fin.lastCases_castSucc, ind, hn] at this
          simp [assign] at hs; omega
        · exact ⟨a, hs⟩

/-- Every clause transition has as many input places as negative literals, and
every probe exactly one: the input-place count the dichotomy is about. -/
theorem probe_input_places (F : CNF A K) (b : Fin A) (q : Fin (A + 1)) :
    0 < (net F).pre (Fin.natAdd K b) q ↔ q = b.castSucc := by
  induction q using Fin.lastCases with
  | last =>
    simp [net]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  | cast a =>
    simp only [net, Fin.addCases_right, Fin.lastCases_castSucc, ind]
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab, Fin.castSucc_inj]

theorem clause_input_places (F : CNF A K) (c : Fin K) (q : Fin (A + 1)) :
    0 < (net F).pre (Fin.castAdd A c) q ↔ ∃ a, q = a.castSucc ∧ F.neg c a = true := by
  induction q using Fin.lastCases with
  | last =>
    simp [net]
    intro a h
    have := congrArg Fin.val h
    simp at this
    omega
  | cast a =>
    simp only [net, Fin.addCases_left, Fin.lastCases_castSucc, ind]
    constructor
    · intro h
      refine ⟨a, rfl, ?_⟩
      cases hn : F.neg c a
      · simp [hn] at h
      · rfl
    · intro ⟨b, hb, hn⟩
      have := Fin.castSucc_inj.mp hb
      subst this
      simp [hn]

end Reduction

end CBMDPetriCapacity
