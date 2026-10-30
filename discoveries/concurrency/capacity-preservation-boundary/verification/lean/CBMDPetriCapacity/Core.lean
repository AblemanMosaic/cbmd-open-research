/-!
# The all-full obstruction in capacity-constrained Petri nets

`CBMD-CON-CAPACITY-PRESERVATION-001` mapped where the chip-firing live-set
characterization transfers and where it fails, by exhaustive census.  This
module proves one boundary outright.

Say a net is **increasing** when every transition strictly increases the count
at some place, and **inert** at a capacity vector when no transition can ever
fire inside the capacity box.  Then an increasing net preserves the
uncapacitated deadlock behaviour exactly when it is inert: the moment such a net
can fire at all, the capacity has invented a deadlock.

The witness is the all-full marking `cap` itself.  Firing any transition from it
would push its strictly-increasing place over capacity, so the marking is
capacity-dead; but any transition whose input requirements fit inside the
capacities is ordinarily enabled there.

This is why chip-firing needs a sink.  A chip-firing vertex's transition sends
chips to its out-neighbours, so it strictly increases a place — unless the
receiver is the absorbing sink, which carries no capacity.  The sink is the only
thing standing between that model and this obstruction.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDPetriCapacity

/-- A Petri net on `P` places and `T` transitions, as consumption and production
multiplicities. -/
structure Net (P T : Nat) where
  pre : Fin T → Fin P → Nat
  post : Fin T → Fin P → Nat

variable {P T : Nat}

/-- A marking assigns a token count to each place. -/
def Marking (P : Nat) := Fin P → Nat

/-- A marking lies inside the capacity box. -/
def Admissible (cap : Fin P → Nat) (m : Marking P) : Prop := ∀ q, m q ≤ cap q

/-- Ordinary (uncapacitated) enabledness. -/
def OrdEnabled (N : Net P T) (m : Marking P) (t : Fin T) : Prop :=
  ∀ q, N.pre t q ≤ m q

/-- Capacity-constrained enabledness: ordinarily enabled, and the result stays
inside the box.  Truncated subtraction is harmless here because the first
conjunct supplies `pre t q ≤ m q`. -/
def CapEnabled (N : Net P T) (cap : Fin P → Nat) (m : Marking P) (t : Fin T) : Prop :=
  OrdEnabled N m t ∧ ∀ q, m q - N.pre t q + N.post t q ≤ cap q

def CapDead (N : Net P T) (cap : Fin P → Nat) (m : Marking P) : Prop :=
  ∀ t, ¬ CapEnabled N cap m t

def OrdDead (N : Net P T) (m : Marking P) : Prop :=
  ∀ t, ¬ OrdEnabled N m t

/-- The capacity invented no deadlock: every admissible capacity-dead marking is
already dead without the capacity.

Quantifying over admissible markings rather than over markings reachable from
admissible ones loses nothing: capacity firing keeps a marking admissible, and
every admissible marking is reachable from itself in zero steps. -/
def Preserves (N : Net P T) (cap : Fin P → Nat) : Prop :=
  ∀ m, Admissible cap m → CapDead N cap m → OrdDead N m

/-! ## The reachability form, and why quantifying over admissible markings is the same

`Preserves` quantifies over admissible markings.  The census that motivated this
module quantifies over markings capacity-reachable from an admissible initial
marking.  Those are the same set, and the two definitions therefore agree -- but
that is a claim about the model, so it is proved rather than asserted. -/

/-- The marking after firing `t`. -/
def fire (N : Net P T) (m : Marking P) (t : Fin T) : Marking P :=
  fun q => m q - N.pre t q + N.post t q

/-- Capacity firing cannot leave the box: that is exactly its second conjunct. -/
theorem fire_admissible {N : Net P T} {cap : Fin P → Nat} {m : Marking P} {t : Fin T}
    (en : CapEnabled N cap m t) : Admissible cap (fire N m t) :=
  fun q => en.2 q

/-- Capacity-reachability. -/
inductive Reach (N : Net P T) (cap : Fin P → Nat) : Marking P → Marking P → Prop
  | refl (m : Marking P) : Reach N cap m m
  | step {m z : Marking P} {t : Fin T} :
      CapEnabled N cap m t → Reach N cap (fire N m t) z → Reach N cap m z

theorem reach_admissible {N : Net P T} {cap : Fin P → Nat} {m z : Marking P}
    (reach : Reach N cap m z) (adm : Admissible cap m) : Admissible cap z := by
  induction reach with
  | refl _ => exact adm
  | step en _ ih => exact ih (fire_admissible en)

/-- The two readings coincide.  Every admissible marking is reachable from
itself, and nothing reachable leaves the box. -/
theorem preserves_iff_reachable_form {N : Net P T} {cap : Fin P → Nat} :
    Preserves N cap ↔
      ∀ m z, Admissible cap m → Reach N cap m z → CapDead N cap z → OrdDead N z := by
  constructor
  · intro pres m z adm reach dead
    exact pres z (reach_admissible reach adm) dead
  · intro h m adm dead
    exact h m m adm (Reach.refl m) dead

/-- Every transition strictly increases the count at some place. -/
def Increasing (N : Net P T) : Prop :=
  ∀ t, ∃ q, N.pre t q < N.post t q

/-- No transition can fire from any admissible marking. -/
def Inert (N : Net P T) (cap : Fin P → Nat) : Prop :=
  ∀ t, ∃ q, cap q < N.pre t q

/-- An inert net has no ordinarily enabled transition at any admissible marking. -/
theorem inert_ordDead {N : Net P T} {cap : Fin P → Nat}
    (inert : Inert N cap) {m : Marking P} (adm : Admissible cap m) :
    OrdDead N m := by
  intro t enabled
  obtain ⟨q, hq⟩ := inert t
  exact Nat.not_lt_of_ge (Nat.le_trans (enabled q) (adm q)) hq

/-- **The all-full marking is capacity-dead** in an increasing net.  Firing any
transition would push its strictly-increasing place past the capacity. -/
theorem increasing_allFull_capDead {N : Net P T} (inc : Increasing N)
    (cap : Fin P → Nat) : CapDead N cap cap := by
  intro t ⟨ord, fits⟩
  obtain ⟨q, hq⟩ := inc t
  have hle : N.pre t q ≤ cap q := ord q
  have := fits q
  omega

/-- **The all-full obstruction.**  An increasing net preserves the uncapacitated
deadlock behaviour exactly when it is inert.  So any increasing net that can
fire at all has a capacity-invented deadlock, and no enlargement of the
capacities removes it: the witness is built from the capacities themselves. -/
theorem increasing_preserves_iff_inert {N : Net P T} (inc : Increasing N)
    (cap : Fin P → Nat) : Preserves N cap ↔ Inert N cap := by
  constructor
  · intro pres t
    by_cases h : ∃ q, cap q < N.pre t q
    · exact h
    · exfalso
      have ord : OrdEnabled N cap t := by
        intro q
        by_cases hq : N.pre t q ≤ cap q
        · exact hq
        · exact absurd ⟨q, Nat.lt_of_not_le hq⟩ h
      exact pres cap (fun q => Nat.le_refl (cap q))
        (increasing_allFull_capDead inc cap) t ord
  · intro inert m adm _
    exact inert_ordDead inert adm

/-- The contrapositive, as the obstruction: an increasing net that can fire has
an invented deadlock at the all-full marking. -/
theorem increasing_firing_breaks_preservation {N : Net P T} (inc : Increasing N)
    (cap : Fin P → Nat) {t : Fin T} (fires : OrdEnabled N cap t) :
    ¬ Preserves N cap := by
  intro pres
  obtain ⟨q, hq⟩ := (increasing_preserves_iff_inert inc cap).mp pres t
  exact Nat.not_lt_of_ge (fires q) hq

end CBMDPetriCapacity
