/-!
# One input place is the whole story

Revision 0.4.0 puts the complexity boundary at the number of **input** places
per transition, and the hardness construction uses only that a transition's
ordinary enabledness is a conjunction over its inputs.  Its outputs play no
part.  So the polynomial side should hold for any number of outputs, which the
flow family of `WeightedFlow` does not cover.

It does, and for a reason that makes the whole single-input case collapse to
one marking.

With a single input place, "m is capacity-dead" is a set of clauses with **one
negative literal each**: `¬(w(t) ≤ m (input t))` together with one positive
literal per place that firing would overflow.  Such a system is closed under
pointwise maximum, so there is a greatest capacity-dead admissible marking, and
since ordinary enabledness is monotone, that one marking decides everything:

  `Preserves  ↔  the greatest capacity-dead admissible marking is ordinarily dead`

`capDead_max` is the closure lemma and is where the single-input hypothesis is
spent; it uses no finiteness.  `preserves_iff_greatest_ordDead` takes the
greatest marking as given — computing it is the lowering iteration, whose
termination is argued in prose from the decreasing measure `Σ m q`.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDPetriCapacity

/-- A net in which every transition consumes from at most one place. -/
structure SNet (P T : Nat) where
  pre : Fin T → Fin P → Nat
  post : Fin T → Fin P → Nat
  input : Fin T → Fin P
  single : ∀ t q, q ≠ input t → pre t q = 0

namespace SNet

variable {P T : Nat}

def Admissible (cap m : Fin P → Nat) : Prop := ∀ q, m q ≤ cap q

def OrdEnabled (N : SNet P T) (m : Fin P → Nat) (t : Fin T) : Prop :=
  ∀ q, N.pre t q ≤ m q

def CapEnabled (N : SNet P T) (cap m : Fin P → Nat) (t : Fin T) : Prop :=
  N.OrdEnabled m t ∧ ∀ q, m q - N.pre t q + N.post t q ≤ cap q

def CapDead (N : SNet P T) (cap m : Fin P → Nat) : Prop :=
  ∀ t, ¬ N.CapEnabled cap m t

def OrdDead (N : SNet P T) (m : Fin P → Nat) : Prop :=
  ∀ t, ¬ N.OrdEnabled m t

def Preserves (N : SNet P T) (cap : Fin P → Nat) : Prop :=
  ∀ m, Admissible cap m → N.CapDead cap m → N.OrdDead m

/-- Ordinary enabledness only improves as the marking grows. -/
theorem ordEnabled_mono {N : SNet P T} {m m' : Fin P → Nat}
    (h : ∀ q, m q ≤ m' q) {t : Fin T} (en : N.OrdEnabled m t) :
    N.OrdEnabled m' t :=
  fun q => Nat.le_trans (en q) (h q)

/-- **Closure under pointwise maximum.**  This is where the single-input
hypothesis is spent: off the input place the consumption is zero, so an
overflow witnessed by the smaller marking is still an overflow for the
maximum. -/
theorem capDead_max {N : SNet P T} {cap m₁ m₂ : Fin P → Nat}
    (a₁ : Admissible cap m₁) (a₂ : Admissible cap m₂)
    (d₁ : N.CapDead cap m₁) (d₂ : N.CapDead cap m₂) :
    Admissible cap (fun q => Nat.max (m₁ q) (m₂ q)) ∧
      N.CapDead cap (fun q => Nat.max (m₁ q) (m₂ q)) := by
  refine ⟨fun q => Nat.max_le.mpr ⟨a₁ q, a₂ q⟩, ?_⟩
  intro t hen
  obtain ⟨en, fits⟩ := hen
  have eni : N.pre t (N.input t) ≤ Nat.max (m₁ (N.input t)) (m₂ (N.input t)) :=
    en (N.input t)
  -- whichever marking attains the maximum at the input place is itself
  -- capacity-enabled at t, which its own deadness forbids
  have main : ∀ mi : Fin P → Nat,
      (∀ q, mi q ≤ Nat.max (m₁ q) (m₂ q)) →
      Nat.max (m₁ (N.input t)) (m₂ (N.input t)) ≤ mi (N.input t) →
      N.CapEnabled cap mi t := by
    intro mi hle hat
    refine ⟨?_, ?_⟩
    · intro q
      by_cases hq : q = N.input t
      · subst hq; exact Nat.le_trans eni hat
      · rw [N.single t q hq]; exact Nat.zero_le _
    · intro q
      have hf : Nat.max (m₁ q) (m₂ q) - N.pre t q + N.post t q ≤ cap q := fits q
      have hm : mi q ≤ Nat.max (m₁ q) (m₂ q) := hle q
      by_cases hq : q = N.input t
      · subst hq
        have : mi (N.input t) = Nat.max (m₁ (N.input t)) (m₂ (N.input t)) :=
          Nat.le_antisymm hm hat
        omega
      · have hz : N.pre t q = 0 := N.single t q hq
        rw [hz] at hf ⊢
        omega
  rcases Nat.le_total (m₂ (N.input t)) (m₁ (N.input t)) with h | h
  · exact d₁ t (main m₁ (fun q => Nat.le_max_left _ _)
      (Nat.max_le.mpr ⟨Nat.le_refl _, h⟩))
  · exact d₂ t (main m₂ (fun q => Nat.le_max_right _ _)
      (Nat.max_le.mpr ⟨h, Nat.le_refl _⟩))

/-- **One marking decides.**  Given the greatest capacity-dead admissible
marking, preservation is equivalent to that single marking being ordinarily
dead.  Computing it is the lowering iteration; here it is taken as given. -/
theorem preserves_iff_greatest_ordDead {N : SNet P T} {cap M : Fin P → Nat}
    (adm : Admissible cap M) (dead : N.CapDead cap M)
    (greatest : ∀ m, Admissible cap m → N.CapDead cap m → ∀ q, m q ≤ M q) :
    N.Preserves cap ↔ N.OrdDead M := by
  constructor
  · intro pres; exact pres M adm dead
  · intro hM m am dm t en
    exact hM t (ordEnabled_mono (greatest m am dm) en)

/-! ## Discharging the greatest-marking hypothesis

`preserves_iff_greatest_ordDead` takes the greatest capacity-dead admissible
marking as given.  `Capped q n` discharges that: it records that *every*
admissible capacity-dead marking holds at most `n` at `q`, and it is generated
by exactly the two things the lowering iteration does — start at the capacities,
and lower a transition's input place whenever that transition would otherwise
be capacity-enabled.

This is the dual of `Forced` in `WeightedFlow`: there the iteration raises and
the certificate is a lower bound, here it lowers and the certificate is an
upper bound.  In both cases the point is that the procedure can emit its own
justification and a checker can validate it, instead of the proof assuming the
procedure did the right thing. -/

/-- `Capped q n`: every admissible capacity-dead marking holds at most `n` at `q`. -/
inductive Capped (N : SNet P T) (cap : Fin P → Nat) : Fin P → Nat → Prop
  | init (q : Fin P) : Capped N cap q (cap q)
  | step {t : Fin T} {u : Fin P → Nat}
      (hu : ∀ q, Capped N cap q (u q))
      (hfit : ∀ q, u q - N.pre t q + N.post t q ≤ cap q) :
      Capped N cap (N.input t) (N.pre t (N.input t) - 1)

/-- **The induction behind the lowering.**  A capped level really is an upper
bound on every admissible capacity-dead marking. -/
theorem capped_ge_of_bad {N : SNet P T} {cap m : Fin P → Nat}
    (adm : Admissible cap m) (dead : N.CapDead cap m)
    {q : Fin P} {n : Nat} (h : Capped N cap q n) : m q ≤ n := by
  induction h with
  | init q => exact adm q
  | @step t u hu hfit ih =>
    by_cases hle : m (N.input t) ≤ N.pre t (N.input t) - 1
    · exact hle
    · exfalso
      have hgt : N.pre t (N.input t) - 1 < m (N.input t) := Nat.lt_of_not_le hle
      refine dead t ⟨?_, ?_⟩
      · intro x
        by_cases hx : x = N.input t
        · subst hx; omega
        · rw [N.single t x hx]; exact Nat.zero_le _
      · intro x
        have hmu : m x ≤ u x := ih x
        have := hfit x
        omega

/-- **Preservation decided by a certified lowering.**  If every entry of `M` is
capped, and `M` is itself admissible and capacity-dead, then `M` is the greatest
such marking and preservation reduces to testing it. -/
theorem preserves_iff_capped_ordDead {N : SNet P T} {cap M : Fin P → Nat}
    (adm : Admissible cap M) (dead : N.CapDead cap M)
    (capped : ∀ q, Capped N cap q (M q)) :
    N.Preserves cap ↔ N.OrdDead M :=
  preserves_iff_greatest_ordDead adm dead
    (fun _m am dm q => capped_ge_of_bad am dm (capped q))

end SNet

end CBMDPetriCapacity
