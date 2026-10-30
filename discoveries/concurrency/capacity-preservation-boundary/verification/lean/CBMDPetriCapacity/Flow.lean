/-!
# A characterization in the draining regime

`Core` proves that a net in which every transition increases some place
preserves the uncapacitated deadlock behaviour exactly when it cannot fire at
all.  The hypothesis fails precisely for transitions that **drain** -- consume
without producing -- and that case was left open.

This settles it for the unit-weight flow family: each transition takes one
token from a place and either puts it in another place or discards it.  The
answer is a filled-set condition, the same shape as the one in
`CBMD-DYN-WEIGHTED-CAPACITY-001`, extended to cope with drains and with places
whose capacity is zero.

A set `S` of places is an **obstruction** when

* every member has positive capacity (`InBox`),
* no drain takes from a member (`NoDrainSource`) -- a drain is never blocked,
  so a member feeding one could always fire,
* every mover out of a member lands in `S` or in a zero-capacity place
  (`Closed`) -- those are the two ways a mover can be blocked,
* some mover takes from a member (`Fires`), or nothing is enabled and there is
  no deadlock to invent.

Then preservation holds exactly when no obstruction exists.  Filling `S` to
capacity and emptying everything else is the witness, so again no enlargement
of the capacities escapes it.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDPetriCapacity

/-- Unit-weight flow net: each transition drains one token from `src t`, and
delivers it to `dst t` when that is `some`. -/
structure Flow (P T : Nat) where
  src : Fin T → Fin P
  dst : Fin T → Option (Fin P)

namespace Flow

variable {P T : Nat}

def OrdEnabled (F : Flow P T) (m : Fin P → Nat) (t : Fin T) : Prop :=
  1 ≤ m (F.src t)

def CapEnabled (F : Flow P T) (cap m : Fin P → Nat) (t : Fin T) : Prop :=
  1 ≤ m (F.src t) ∧ ∀ d, F.dst t = some d → m d + 1 ≤ cap d

def Admissible (cap m : Fin P → Nat) : Prop := ∀ q, m q ≤ cap q

def Preserves (F : Flow P T) (cap : Fin P → Nat) : Prop :=
  ∀ m, Admissible cap m → (∀ t, ¬ F.CapEnabled cap m t) → ∀ t, ¬ F.OrdEnabled m t

/-- A set of places that can be held full forever. -/
structure Obstruction (F : Flow P T) (cap : Fin P → Nat) where
  mem : Fin P → Prop
  inBox : ∀ q, mem q → 1 ≤ cap q
  noDrainSource : ∀ t, F.dst t = none → ¬ mem (F.src t)
  closed : ∀ t d, F.dst t = some d → mem (F.src t) → mem d ∨ cap d = 0
  fires : ∃ t d, F.dst t = some d ∧ mem (F.src t)

/-- **Obstruction ⇒ failure.**  Fill `S` to capacity, empty the rest. -/
theorem obstruction_breaks {F : Flow P T} {cap : Fin P → Nat}
    (O : F.Obstruction cap) : ¬ F.Preserves cap := by
  classical
  intro pres
  let m : Fin P → Nat := fun q => if O.mem q then cap q else 0
  have adm : Admissible cap m := by
    intro q
    by_cases h : O.mem q <;> simp [m, h]
  have dead : ∀ t, ¬ F.CapEnabled cap m t := by
    intro t ⟨pos, fits⟩
    by_cases hs : O.mem (F.src t)
    · cases hd : F.dst t with
      | none => exact O.noDrainSource t hd hs
      | some d =>
        have hfit := fits d hd
        rcases O.closed t d hd hs with hmem | hzero
        · have : m d = cap d := by simp [m, hmem]
          omega
        · have : m d = 0 := by
            by_cases h : O.mem d <;> simp [m, h, hzero]
          omega
    · have : m (F.src t) = 0 := by simp [m, hs]
      omega
  obtain ⟨t, d, hd, hs⟩ := O.fires
  have : m (F.src t) = cap (F.src t) := by simp [m, hs]
  have : (1 : Nat) ≤ m (F.src t) := by rw [this]; exact O.inBox _ hs
  exact pres m adm dead t this

/-- **Failure ⇒ obstruction.**  Take the places the failing marking occupies. -/
noncomputable def obstructionOfFailure {F : Flow P T} {cap : Fin P → Nat}
    {m : Fin P → Nat} (adm : Admissible cap m)
    (dead : ∀ t, ¬ F.CapEnabled cap m t)
    {t₀ : Fin T} (live : F.OrdEnabled m t₀) :
    F.Obstruction cap := by
  classical
  have hd₀ : ∃ d, F.dst t₀ = some d := by
    cases hd : F.dst t₀ with
    | none => exact absurd ⟨live, fun d hdd => by rw [hd] at hdd; exact absurd hdd (by simp)⟩ (dead t₀)
    | some d => exact ⟨d, rfl⟩
  refine
    { mem := fun q => 1 ≤ m q
      inBox := fun q hq => Nat.le_trans hq (adm q)
      noDrainSource := ?_
      closed := ?_
      fires := ⟨t₀, hd₀.choose, hd₀.choose_spec, live⟩ }
  · intro t hnone hs
    exact dead t ⟨hs, fun d hdd => by rw [hnone] at hdd; exact absurd hdd (by simp)⟩
  · intro t d hd hs
    have notcap := dead t
    have : ¬ (∀ d', F.dst t = some d' → m d' + 1 ≤ cap d') := fun h => notcap ⟨hs, h⟩
    have hfail : ¬ (m d + 1 ≤ cap d) := by
      intro h
      exact this (fun d' hd' => by
        have : d' = d := by rw [hd] at hd'; exact (Option.some.inj hd').symm
        subst this; exact h)
    have hle := adm d
    by_cases hz : cap d = 0
    · exact Or.inr hz
    · exact Or.inl (by omega)

/-- **The characterization.**  Preservation holds exactly when no obstruction
exists. -/
theorem preserves_iff_no_obstruction {F : Flow P T} (cap : Fin P → Nat) :
    F.Preserves cap ↔ (F.Obstruction cap → False) := by
  classical
  constructor
  · intro pres O
    exact obstruction_breaks O pres
  · intro none m adm dead t live
    exact none (obstructionOfFailure adm dead live)

end Flow

end CBMDPetriCapacity
