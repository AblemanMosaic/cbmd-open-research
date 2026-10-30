/-!
# Weighted flow: the obstruction carries levels, and the least closure decides

`Flow` characterizes unit-weight flow nets by a SET of places held full.  With
weights that normalization breaks: raising a place to its capacity can make a
transition ordinarily enabled that was not, and then nothing blocks it.  So the
obstruction has to carry **levels** rather than membership.

A weighted flow net takes `take t` tokens from `src t` and, when `dst t` is
`some d`, delivers `give t` of them to `d`.  Reading blocking as an implication,

  `take t ≤ ℓ (src t)  →  cap d < ℓ d + give t`

makes the obstruction a monotone closure condition on a level function, and
suggests an algorithm: seed `ℓ (src t₀) = take t₀`, close, and test.  The
content of this module is that the test is both sound and complete:

* `obstruction_breaks` — any level function satisfying the conditions is a
  failing marking;
* `obstructionOfFailure` — any failing marking is one;
* `least_closure_is_complete` — if ANY admissible capacity-dead marking lies
  above the seeded closure, that closure is itself an obstruction.  So testing
  the least closure, once per transition, misses nothing.

The third is what makes the algorithm correct rather than merely sound.  Two
honest notes on it.

The hypothesis that the witnessing marking fires `t₀` is **not needed**: the
seed already supplies `fires`, and the proof uses only `ℓ ≤ m` and the deadness
of `m`.  The lemma is therefore a little stronger than the algorithm requires,
and carrying the unused hypothesis would have made it look weaker than it is.

The `least` hypothesis — that `ℓ` lies below the witnessing marking — is where
the construction of the closure would go.  It holds by induction along the
closure: the seed is below `m` because `m` fires `t₀`, and each closure step
raises `ℓ d` only to `cap d - give t + 1`, which `m d` already exceeds because
`m` is capacity-dead at `t`.  That induction, and the termination of the
iteration from the decreasing measure `Σ (cap q - ℓ q)`, are argued in prose
and are **not** compiled here.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDPetriCapacity

/-- Weighted flow net. -/
structure WFlow (P T : Nat) where
  src : Fin T → Fin P
  dst : Fin T → Option (Fin P)
  take : Fin T → Nat
  give : Fin T → Nat

namespace WFlow

variable {P T : Nat}

def OrdEnabled (F : WFlow P T) (m : Fin P → Nat) (t : Fin T) : Prop :=
  F.take t ≤ m (F.src t)

def CapEnabled (F : WFlow P T) (cap m : Fin P → Nat) (t : Fin T) : Prop :=
  F.take t ≤ m (F.src t) ∧ ∀ d, F.dst t = some d → m d + F.give t ≤ cap d

def Admissible (cap m : Fin P → Nat) : Prop := ∀ q, m q ≤ cap q

def Preserves (F : WFlow P T) (cap : Fin P → Nat) : Prop :=
  ∀ m, Admissible cap m → (∀ t, ¬ F.CapEnabled cap m t) → ∀ t, ¬ F.OrdEnabled m t

/-- A level function that can be held forever while something is still enabled. -/
structure Obstruction (F : WFlow P T) (cap : Fin P → Nat) where
  level : Fin P → Nat
  inBox : ∀ q, level q ≤ cap q
  drainBlocked : ∀ t, F.dst t = none → level (F.src t) < F.take t
  moverBlocked : ∀ t d, F.dst t = some d → F.take t ≤ level (F.src t) →
    cap d < level d + F.give t
  fires : ∃ t, F.take t ≤ level (F.src t)

theorem obstruction_breaks {F : WFlow P T} {cap : Fin P → Nat}
    (O : F.Obstruction cap) : ¬ F.Preserves cap := by
  intro pres
  obtain ⟨t₀, h₀⟩ := O.fires
  refine pres O.level O.inBox ?_ t₀ h₀
  intro t ⟨pos, fits⟩
  cases hd : F.dst t with
  | none => exact Nat.not_lt_of_ge pos (O.drainBlocked t hd)
  | some d =>
    have := fits d hd
    have := O.moverBlocked t d hd pos
    omega

/-- Every failing marking is itself an obstruction, with its own levels. -/
def obstructionOfFailure {F : WFlow P T} {cap m : Fin P → Nat}
    (adm : Admissible cap m) (dead : ∀ t, ¬ F.CapEnabled cap m t)
    {t₀ : Fin T} (live : F.OrdEnabled m t₀) :
    F.Obstruction cap where
  level := m
  inBox := adm
  drainBlocked t hd := by
    by_cases h : F.take t ≤ m (F.src t)
    · exact absurd ⟨h, fun d hdd => by rw [hd] at hdd; exact absurd hdd (by simp)⟩ (dead t)
    · exact Nat.lt_of_not_le h
  moverBlocked t d hd pos := by
    have : ¬ (∀ d', F.dst t = some d' → m d' + F.give t ≤ cap d') :=
      fun h => dead t ⟨pos, h⟩
    by_cases h : m d + F.give t ≤ cap d
    · exact absurd (fun d' hd' => by
        have : d' = d := by rw [hd] at hd'; exact (Option.some.inj hd').symm
        subst this; exact h) this
    · exact Nat.lt_of_not_le h
  fires := ⟨t₀, live⟩

theorem preserves_iff_no_obstruction {F : WFlow P T} (cap : Fin P → Nat) :
    F.Preserves cap ↔ (F.Obstruction cap → False) := by
  constructor
  · intro pres O; exact obstruction_breaks O pres
  · intro none m adm dead t live; exact none (obstructionOfFailure adm dead live)

/-- **The least closure decides.**  Suppose `ℓ` is seeded at `t₀`, is closed
under the blocking implication, and lies below some admissible capacity-dead
marking.  Then `ℓ` is itself an obstruction, so an algorithm that builds the
least closure for each `t₀` and tests it is complete, not merely sound.

The witnessing marking need not fire `t₀`: the seed supplies that. -/
def least_closure_is_complete {F : WFlow P T} {cap : Fin P → Nat}
    {ℓ : Fin P → Nat} {t₀ : Fin T}
    (seed : F.take t₀ ≤ ℓ (F.src t₀))
    (closed : ∀ t d, F.dst t = some d → F.take t ≤ ℓ (F.src t) →
      cap d < ℓ d + F.give t)
    {m : Fin P → Nat}
    (adm : Admissible cap m) (dead : ∀ t, ¬ F.CapEnabled cap m t)
    (least : ∀ q, ℓ q ≤ m q) :
    F.Obstruction cap where
  level := ℓ
  inBox q := Nat.le_trans (least q) (adm q)
  drainBlocked t hd := by
    -- the drain is blocked at `m`, and `ℓ` is below `m`
    have hm : ¬ F.take t ≤ m (F.src t) := by
      intro h
      exact dead t ⟨h, fun d hdd => by rw [hd] at hdd; exact absurd hdd (by simp)⟩
    exact Nat.lt_of_le_of_lt (least (F.src t)) (Nat.lt_of_not_le hm)
  moverBlocked := closed
  fires := ⟨t₀, seed⟩

/-! ## Discharging the leastness hypothesis

`least_closure_is_complete` assumes that `ℓ` lies below the witnessing marking.
That assumption is where the construction of the closure would go, and leaving
it as an assumption leaves the algorithm's completeness resting on prose.  It
can be discharged.

`Forced q n` records that *any* admissible capacity-dead marking firing `t₀`
must hold at least `n` tokens at `q`.  It is generated by the seed and by one
step per blocked mover, which is exactly what the closure iteration does, so a
level function produced by that iteration comes with a `Forced` derivation for
each of its entries.  `forced_le_of_bad` is the induction that was previously
only argued in prose.

The guard `give t ≤ cap d` on the step is not decoration.  A mover whose
production exceeds the destination's capacity is blocked whatever the
destination holds, so it forces nothing; without the guard, truncated
subtraction would turn `cap d - give t + 1` into `1` and claim a token that
need not be there. -/

/-- `Forced q n`: every admissible capacity-dead marking that fires `t₀` holds
at least `n` at `q`. -/
inductive Forced (F : WFlow P T) (cap : Fin P → Nat) (t₀ : Fin T) :
    Fin P → Nat → Prop
  | seed : Forced F cap t₀ (F.src t₀) (F.take t₀)
  | step {t : Fin T} {d : Fin P} {n : Nat}
      (hd : F.dst t = some d) (hgive : F.give t ≤ cap d)
      (hn : F.take t ≤ n) (h : Forced F cap t₀ (F.src t) n) :
      Forced F cap t₀ d (cap d - F.give t + 1)

/-- **The induction behind the closure.**  A forced level really is a lower
bound on every failing marking that fires `t₀`. -/
theorem forced_le_of_bad {F : WFlow P T} {cap m : Fin P → Nat} {t₀ : Fin T}
    (dead : ∀ t, ¬ F.CapEnabled cap m t)
    (live : F.OrdEnabled m t₀)
    {q : Fin P} {n : Nat} (h : Forced F cap t₀ q n) : n ≤ m q := by
  induction h with
  | seed => exact live
  | @step t d n hd hgive hn _ ih =>
    have hsrc : F.take t ≤ m (F.src t) := Nat.le_trans hn ih
    have : ¬ (∀ d', F.dst t = some d' → m d' + F.give t ≤ cap d') :=
      fun hall => dead t ⟨hsrc, hall⟩
    have hfail : ¬ (m d + F.give t ≤ cap d) := by
      intro hle
      exact this (fun d' hd' => by
        have : d' = d := by rw [hd] at hd'; exact (Option.some.inj hd').symm
        subst this; exact hle)
    have hlt : cap d < m d + F.give t := Nat.lt_of_not_le hfail
    omega

/-- **Completeness, with nothing assumed about `ℓ` that the algorithm does not
produce.**  A level function whose every entry is either zero or forced, which
is seeded at `t₀` and closed under the blocking implication, is an obstruction
as soon as any failing marking fires `t₀`. -/
def justified_closure_is_complete {F : WFlow P T} {cap : Fin P → Nat}
    {ℓ : Fin P → Nat} {t₀ : Fin T}
    (seed : F.take t₀ ≤ ℓ (F.src t₀))
    (closed : ∀ t d, F.dst t = some d → F.take t ≤ ℓ (F.src t) →
      cap d < ℓ d + F.give t)
    (justified : ∀ q, ℓ q = 0 ∨ Forced F cap t₀ q (ℓ q))
    {m : Fin P → Nat}
    (adm : Admissible cap m) (dead : ∀ t, ¬ F.CapEnabled cap m t)
    (live : F.OrdEnabled m t₀) :
    F.Obstruction cap :=
  least_closure_is_complete seed closed adm dead
    (fun q => by
      rcases justified q with hz | hf
      · rw [hz]; exact Nat.zero_le _
      · exact forced_le_of_bad dead live hf)

end WFlow

end CBMDPetriCapacity
