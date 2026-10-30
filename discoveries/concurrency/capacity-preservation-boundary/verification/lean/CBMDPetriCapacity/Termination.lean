import CBMDPetriCapacity.SingleInput

/-!
# The lowering iteration terminates, and produces its own certificate

`SingleInput` reduces preservation for a single-input net to one marking: the
greatest admissible capacity-dead marking.  `Capped` certifies that a candidate
is greatest, and `preserves_iff_capped_ordDead` turns a certified candidate
into a verdict.  What was left in prose is that such a candidate **exists** —
that lowering from the capacities halts.

It does, and the argument is the obvious one: each lowering strictly drops the
total token count, which is a natural number.  Compiling it needs a sum over
the places, which is built here rather than imported, and then strong induction
on that sum.

`exists_capped_capDead` is the result: from the capacities there is always a
reachable admissible capacity-dead marking all of whose levels are `Capped`.
Together with `preserves_iff_capped_ordDead` the single-input case is decided
with nothing left to prose.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDPetriCapacity

namespace SNet

variable {P T : Nat}

/-! ## A sum over the places -/

/-- `sumBelow f n = f 0 + ... + f (n-1)`. -/
def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => f n + sumBelow f n

theorem sumBelow_le {f g : Nat → Nat} {n : Nat}
    (h : ∀ i, i < n → f i ≤ g i) : sumBelow f n ≤ sumBelow g n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    exact Nat.add_le_add (h n (Nat.lt_succ_self n))
      (ih (fun i hi => h i (Nat.lt_succ_of_lt hi)))

theorem sumBelow_lt {f g : Nat → Nat} {n j : Nat}
    (hle : ∀ i, i < n → f i ≤ g i) (hj : j < n) (hlt : f j < g j) :
    sumBelow f n < sumBelow g n := by
  induction n with
  | zero => exact absurd hj (Nat.not_lt_zero j)
  | succ n ih =>
    by_cases hjn : j = n
    · subst hjn
      have := sumBelow_le (f := f) (g := g) (n := j)
        (fun i hi => hle i (Nat.lt_succ_of_lt hi))
      exact Nat.add_lt_add_of_lt_of_le hlt this
    · have hj' : j < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hjn
      exact Nat.add_lt_add_of_le_of_lt (hle n (Nat.lt_succ_self n))
        (ih (fun i hi => hle i (Nat.lt_succ_of_lt hi)) hj')

/-- Total tokens in a marking. -/
def total (m : Fin P → Nat) : Nat :=
  sumBelow (fun i => if h : i < P then m ⟨i, h⟩ else 0) P

theorem total_lt {m m' : Fin P → Nat} (hle : ∀ q, m' q ≤ m q)
    {j : Fin P} (hlt : m' j < m j) : total m' < total m := by
  refine sumBelow_lt (j := j.val) ?_ j.isLt ?_
  · intro i hi
    simp only [hi, dite_true]
    exact hle ⟨i, hi⟩
  · simp only [j.isLt, dite_true]
    exact hlt

/-! ## The iteration halts -/

/-- Lowering one transition's input place to just under its own weight. -/
def lower (N : SNet P T) (m : Fin P → Nat) (t : Fin T) : Fin P → Nat :=
  fun q => if q = N.input t then N.pre t (N.input t) - 1 else m q

theorem lower_le {N : SNet P T} {m : Fin P → Nat} {t : Fin T}
    (en : N.CapEnabled cap m t) : ∀ q, N.lower m t q ≤ m q := by
  intro q
  by_cases hq : q = N.input t
  · subst hq
    have h1 : N.pre t (N.input t) ≤ m (N.input t) := en.1 (N.input t)
    have h2 : N.lower m t (N.input t) = N.pre t (N.input t) - 1 := by
      simp [lower]
    omega
  · have : N.lower m t q = m q := by simp [lower, hq]
    omega

theorem lower_lt {N : SNet P T} {cap m : Fin P → Nat} {t : Fin T}
    (en : N.CapEnabled cap m t) (pos : 0 < N.pre t (N.input t)) :
    N.lower m t (N.input t) < m (N.input t) := by
  have h1 : N.pre t (N.input t) ≤ m (N.input t) := en.1 (N.input t)
  have h2 : N.lower m t (N.input t) = N.pre t (N.input t) - 1 := by
    simp [lower]
  omega

/-- The induction behind termination, with an explicit bound.  Each lowering
strictly drops the total token count, so a bound on that count bounds the
number of lowerings. -/
theorem exists_capped_capDead_aux {N : SNet P T} {cap : Fin P → Nat}
    (positive : ∀ t, 0 < N.pre t (N.input t)) :
    ∀ (fuel : Nat) (m : Fin P → Nat), Admissible cap m →
      (∀ q, Capped N cap q (m q)) → total m ≤ fuel →
      ∃ M, Admissible cap M ∧ N.CapDead cap M ∧ (∀ q, Capped N cap q (M q)) := by
  classical
  intro fuel
  induction fuel with
  | zero =>
    intro m adm capped hfuel
    by_cases dead : ∀ t, ¬ N.CapEnabled cap m t
    · exact ⟨m, adm, dead, capped⟩
    · exfalso
      obtain ⟨t, ht⟩ : ∃ t, N.CapEnabled cap m t :=
        Classical.byContradiction (fun hno => dead (fun t h => hno ⟨t, h⟩))
      have hdec : total (N.lower m t) < total m :=
        total_lt (lower_le (cap := cap) ht) (lower_lt ht (positive t))
      omega
  | succ n ih =>
    intro m adm capped hfuel
    by_cases dead : ∀ t, ¬ N.CapEnabled cap m t
    · exact ⟨m, adm, dead, capped⟩
    · obtain ⟨t, ht⟩ : ∃ t, N.CapEnabled cap m t :=
        Classical.byContradiction (fun hno => dead (fun t h => hno ⟨t, h⟩))
      have hle := lower_le (cap := cap) ht
      have hdec : total (N.lower m t) < total m :=
        total_lt hle (lower_lt ht (positive t))
      refine ih (N.lower m t) (fun q => Nat.le_trans (hle q) (adm q)) ?_ (by omega)
      intro q
      by_cases hq : q = N.input t
      · subst hq
        have : N.lower m t (N.input t) = N.pre t (N.input t) - 1 := by simp [lower]
        rw [this]
        exact Capped.step (N := N) (cap := cap) (t := t) (u := m) capped ht.2
      · have : N.lower m t q = m q := by simp [lower, hq]
        rw [this]
        exact capped q

/-- **The procedure of revision 0.6.0 halts.**  From the capacities — every
entry `Capped` by `Capped.init` — lowering reaches an admissible capacity-dead
marking whose levels are all `Capped`, which is what
`preserves_iff_capped_ordDead` consumes. -/
theorem exists_capped_capDead {N : SNet P T} (cap : Fin P → Nat)
    (positive : ∀ t, 0 < N.pre t (N.input t)) :
    ∃ M, Admissible cap M ∧ N.CapDead cap M ∧ (∀ q, Capped N cap q (M q)) :=
  exists_capped_capDead_aux positive (total cap) cap
    (fun q => Nat.le_refl (cap q)) (fun q => Capped.init q) (Nat.le_refl _)

/-- **The single-input case, decided, with nothing left in prose.**  There is a
marking `M`, reached from the capacities by lowering, such that preservation
holds exactly when `M` is ordinarily dead.

The hypothesis `positive` says each transition really does consume from the
place named as its input; without it a "transition" with zero consumption
everywhere is always enabled and the lowering has nothing to lower. -/
theorem preserves_decided_by_lowering {N : SNet P T} (cap : Fin P → Nat)
    (positive : ∀ t, 0 < N.pre t (N.input t)) :
    ∃ M, Admissible cap M ∧ N.CapDead cap M ∧ (N.Preserves cap ↔ N.OrdDead M) := by
  obtain ⟨M, adm, dead, capped⟩ := exists_capped_capDead (N := N) cap positive
  exact ⟨M, adm, dead, preserves_iff_capped_ordDead adm dead capped⟩

end SNet

end CBMDPetriCapacity
