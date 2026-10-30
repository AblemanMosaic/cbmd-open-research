import CBMDPetriCapacity.Guard

/-!
# Free choice does not help

Free-choice nets are the classical subclass where many Petri-net problems
become tractable.  This module shows capacity preservation is not one of
them: the hardness of revision 0.4.0 survives in **strict free-choice** nets
with unit weights, every capacity `1`, and one or two input places per
transition.

## The construction

For a CNF `G` on `n` atoms with `K` clauses: places `x_i` (at `i`), `x̄_i`
(at `n+i`) and `g` (at `n+n`), all of capacity `1`.  Transitions
`Fin (n+n+K)`:

| index | inputs | outputs | blocked exactly when |
|---|---|---|---|
| `i`     | `x_i, x̄_i` | — | not both hold |
| `n+i`   | `g` | `x_i, x̄_i` | `g` empty, or `x_i` or `x̄_i` holds |
| `n+n+k` | `g` | `x_a` for each `a ∈ k`, `x̄_a` for each `¬a ∈ k` | `g` empty, or some literal of clause `k` holds |

The probes and the zero-capacity place of `Reduction.lean` are gone: a bad
marking must ordinarily enable *something*, the first family can never be
ordinarily enabled while capacity-dead (it has no outputs), so what is enabled
is a `g`-transition, which forces `g`.

**Free choice.** The only place with more than one output transition is `g`,
and every transition consuming from `g` consumes from `g` alone.

**The middle family is nearly idle.** The backward direction never uses it,
and it is needed in the forward direction only to have a `g`-transition at all
when `K = 0`.  This mirrors the guard family found idle in revision 0.9.0.

`0 < n` is assumed: with no atoms and no clauses the net has no transitions and
preserves vacuously, while the empty CNF is satisfiable.
-/

namespace CBMDPetriCapacity

namespace FreeChoice

open Reduction

variable {n K : Nat}

def fpre (c : Fin (n + n + K)) (q : Fin (n + n + 1)) : Nat :=
  if c.val < n then ind (decide (q.val = c.val) || decide (q.val = n + c.val))
  else ind (decide (q.val = n + n))

def fpost (G : CNF n K) (c : Fin (n + n + K)) (q : Fin (n + n + 1)) : Nat :=
  if c.val < n then 0
  else if c.val < n + n then ind (decide (q.val = c.val - n) || decide (q.val = n + (c.val - n)))
  else if hk : c.val - (n + n) < K then
    if hq : q.val < n then ind (G.pos ⟨c.val - (n + n), hk⟩ ⟨q.val, hq⟩)
    else if hq' : q.val < n + n then ind (G.neg ⟨c.val - (n + n), hk⟩ ⟨q.val - n, by omega⟩)
    else 0
  else 0

def fnet (G : CNF n K) : Net (n + n + 1) (n + n + K) := ⟨fpre, fpost G⟩

def fcap : Fin (n + n + 1) → Nat := fun _ => 1

theorem ind_le (b : Bool) : ind b ≤ 1 := by cases b <;> simp [ind]

/-- Strict free choice: a place shared by two distinct transitions is the only
input place of each. -/
theorem free_choice (G : CNF n K) (t t' : Fin (n + n + K)) (q : Fin (n + n + 1))
    (ht : 0 < (fnet G).pre t q) (ht' : 0 < (fnet G).pre t' q) (ne : t ≠ t') :
    ∀ r, 0 < (fnet G).pre t r → r = q := by
  simp only [fnet, fpre] at ht ht' ⊢
  by_cases a : t.val < n
  · by_cases b : t'.val < n
    · simp only [a, b, ite_true, ind] at ht ht'
      split at ht <;> split at ht' <;> simp_all
      exact absurd (Fin.ext (by omega)) ne
    · simp only [a, b, ite_true, ite_false, ind] at ht ht'
      split at ht <;> split at ht' <;> simp_all <;> omega
  · intro r hr
    simp only [a, ite_false, ind] at ht hr
    split at ht <;> split at hr <;> simp_all
    exact Fin.ext (by omega)

/-- Every transition has one or two input places. -/
theorem input_places (G : CNF n K) (t : Fin (n + n + K)) :
    (∃ q, 0 < (fnet G).pre t q) ∧
      ∀ a b d, 0 < (fnet G).pre t a → 0 < (fnet G).pre t b → 0 < (fnet G).pre t d →
        a = b ∨ a = d ∨ b = d := by
  have key : ∃ u w : Nat, ∀ q, 0 < (fnet G).pre t q → q.val = u ∨ q.val = w := by
    simp only [fnet, fpre]
    split
    · refine ⟨t.val, n + t.val, fun q h => ?_⟩
      simp only [ind] at h; split at h <;> simp_all
    · refine ⟨n + n, n + n, fun q h => ?_⟩
      simp only [ind] at h; split at h <;> simp_all
  refine ⟨?_, ?_⟩
  · simp only [fnet, fpre]
    split
    · exact ⟨⟨t.val, by omega⟩, by simp [ind]⟩
    · exact ⟨⟨n + n, by omega⟩, by simp [ind]⟩
  · obtain ⟨u, w, hk⟩ := key
    intro a b d ha hb hd
    have := hk a ha; have := hk b hb; have := hk d hd
    by_cases e1 : a.val = b.val
    · exact Or.inl (Fin.ext e1)
    by_cases e2 : a.val = d.val
    · exact Or.inr (Or.inl (Fin.ext e2))
    · exact Or.inr (Or.inr (Fin.ext (by omega)))

/-- The marking of an assignment: `x_i ↦ σ i`, `x̄_i ↦ ¬σ i`, `g ↦ 1`. -/
def fmark (σ : Fin n → Bool) (q : Fin (n + n + 1)) : Nat :=
  if h : q.val < n then ind (σ ⟨q.val, h⟩)
  else if h' : q.val < n + n then ind (!σ ⟨q.val - n, by omega⟩)
  else 1

theorem fmark_admissible (σ : Fin n → Bool) : Admissible fcap (fmark σ) := by
  intro q
  simp only [fmark, fcap]
  split
  · exact ind_le _
  split
  · exact ind_le _
  · exact Nat.le_refl _

theorem satisfiable_not_preserves (G : CNF n K) (hn : 0 < n) (sat : Satisfiable G) :
    ¬ Preserves (fnet G) fcap := by
  obtain ⟨σ, hs⟩ := sat
  intro pres
  have dead : CapDead (fnet G) fcap (fmark σ) := by
    intro t ⟨ord, fits⟩
    by_cases a : t.val < n
    · -- both x_t and x̄_t would have to hold
      have h1 := ord ⟨t.val, by omega⟩
      have h2 := ord ⟨n + t.val, by omega⟩
      have e1 : ¬ n + t.val < n := by omega
      have e2 : n + t.val < n + n := by omega
      have e3 : n + t.val - n = t.val := by omega
      simp only [fnet, fpre, fmark, a, e1, e2, e3, ite_true, dite_true, dite_false,
        decide_true, Bool.true_or, Bool.or_true, ind] at h1 h2
      cases hσ : σ ⟨t.val, a⟩ <;> simp_all
    by_cases b : t.val < n + n
    · have hi : t.val - n < n := by omega
      cases hσ : σ ⟨t.val - n, hi⟩
      · have h := fits ⟨n + (t.val - n), by omega⟩
        have e1 : ¬ n + (t.val - n) < n := by omega
        have e2 : n + (t.val - n) < n + n := by omega
        have e3 : n + (t.val - n) - n = t.val - n := by omega
        have e4 : ¬ n + (t.val - n) = n + n := by omega
        simp only [fnet, fpre, fpost, fcap, fmark, a, b, e1, e2, e3, e4, ite_true, ite_false,
          dite_true, dite_false, decide_true, decide_false, Bool.or_true, ind, hσ] at h
        simp at h
      · have h := fits ⟨t.val - n, by omega⟩
        have e4 : ¬ t.val - n = n + n := by omega
        simp only [fnet, fpre, fpost, fcap, fmark, a, b, hi, e4, ite_true, ite_false,
          dite_true, decide_true, decide_false, Bool.true_or, ind, hσ] at h
        simp at h
    · have hk : t.val - (n + n) < K := by omega
      obtain ⟨x, hx⟩ := hs ⟨t.val - (n + n), hk⟩
      rcases hx with ⟨hneg, hv⟩ | ⟨hpos, hv⟩
      · have h := fits ⟨n + x.val, by omega⟩
        have e1 : ¬ n + x.val < n := by omega
        have e2 : n + x.val < n + n := by omega
        have e4 : ¬ n + x.val = n + n := by omega
        have ex : (⟨n + x.val - n, by omega⟩ : Fin n) = x := Fin.ext (by simp)
        simp only [fnet, fpre, fpost, fcap, fmark, a, b, hk, e1, e2, e4, ex, ite_false,
          dite_true, dite_false, decide_false, ind, hneg, hv] at h
        simp at h
      · have h := fits ⟨x.val, by omega⟩
        have e4 : ¬ x.val = n + n := by omega
        simp only [fnet, fpre, fpost, fcap, fmark, a, b, hk, x.isLt, e4, ite_false,
          dite_true, decide_false, ind, hpos, hv] at h
        simp at h
  -- the middle transition at index n is ordinarily enabled: g holds
  apply pres (fmark σ) (fmark_admissible σ) dead ⟨n, by omega⟩
  intro q
  have a : ¬ n < n := Nat.lt_irrefl n
  simp only [fnet, fpre, a, ite_false, ind]
  split
  · rename_i h
    simp at h
    have : q.val = n + n := h
    have h1 : ¬ n + n < n := by omega
    have h2 : ¬ n + n < n + n := by omega
    simp [fmark, this, h1, h2]
  · exact Nat.zero_le _

theorem not_preserves_satisfiable (G : CNF n K) (np : ¬ Preserves (fnet G) fcap) :
    Satisfiable G := by
  -- extract a bad marking
  have : ∃ m, Admissible fcap m ∧ CapDead (fnet G) fcap m ∧ ∃ t, OrdEnabled (fnet G) m t := by
    apply Classical.byContradiction
    intro h
    apply np
    intro m adm dead t ord
    exact h ⟨m, adm, dead, t, ord⟩
  obtain ⟨m, adm, dead, t, ord⟩ := this
  have le1 : ∀ q, m q ≤ 1 := adm
  -- first-family transitions are never ordinarily enabled at a capacity-dead marking
  have first_blocked : ∀ i : Fin (n + n + K), i.val < n → ¬ OrdEnabled (fnet G) m i := by
    intro i hi o
    apply dead i
    refine ⟨o, fun q => ?_⟩
    simp only [fnet, fpost, hi, ite_true, Nat.add_zero]
    exact Nat.le_trans (Nat.sub_le _ _) (le1 q)
  have tn : ¬ t.val < n := fun h => first_blocked t h ord
  have gpos : 0 < m ⟨n + n, by omega⟩ := by
    have := ord ⟨n + n, by omega⟩
    simp [fnet, fpre, tn, ind] at this
    omega
  refine ⟨fun i => decide (0 < m ⟨i.val, by omega⟩), fun k => ?_⟩
  -- clause k's transition is ordinarily enabled (its only input is g), so it overflows
  let c : Fin (n + n + K) := ⟨n + n + k.val, by omega⟩
  have c1 : ¬ c.val < n := by simp only [c]; omega
  have c2 : ¬ c.val < n + n := by simp only [c]; omega
  have hk : c.val - (n + n) < K := by simp only [c]; omega
  have ek : (⟨c.val - (n + n), hk⟩ : Fin K) = k := Fin.ext (by simp [c])
  have oc : OrdEnabled (fnet G) m c := by
    intro q
    simp only [fnet, fpre, c1, ite_false, ind]
    split
    · rename_i h
      simp at h
      have : q = ⟨n + n, by omega⟩ := Fin.ext h
      rw [this]; omega
    · exact Nat.zero_le _
  have : ¬ ∀ q, m q - (fnet G).pre c q + (fnet G).post c q ≤ fcap q :=
    fun fits => dead c ⟨oc, fits⟩
  have hex : ∃ q, ¬ (m q - (fnet G).pre c q + (fnet G).post c q ≤ fcap q) :=
    Classical.byContradiction fun h =>
      this (fun q => Classical.byContradiction fun hq => h ⟨q, hq⟩)
  obtain ⟨q, hq⟩ := hex
  simp only [fnet, fpre, fpost, fcap, c1, c2, hk, ite_false, dite_true, ek] at hq
  have mle := le1 q
  by_cases q1 : q.val < n
  · simp only [q1, dite_true, ind] at hq
    have hgq : ¬ q.val = n + n := by omega
    simp only [hgq, decide_false] at hq
    cases hp : G.pos k ⟨q.val, q1⟩
    · simp [hp] at hq; all_goals omega
    · refine ⟨⟨q.val, q1⟩, Or.inr ⟨hp, ?_⟩⟩
      simp [hp] at hq
      simp only [decide_eq_true_eq]
      have e : (⟨q.val, by omega⟩ : Fin (n + n + 1)) = q := Fin.ext rfl
      rw [e]; omega
  by_cases q2 : q.val < n + n
  · simp only [q1, q2, dite_true, dite_false, ind] at hq
    have hgq : ¬ q.val = n + n := by omega
    simp only [hgq, decide_false] at hq
    cases hneg : G.neg k ⟨q.val - n, by omega⟩
    · simp [hneg] at hq; all_goals omega
    · refine ⟨⟨q.val - n, by omega⟩, Or.inl ⟨hneg, ?_⟩⟩
      simp [hneg] at hq
      have mq : m q = 1 := by omega
      have fb := first_blocked ⟨q.val - n, by omega⟩ (by simp only; omega)
      simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
      apply Classical.byContradiction
      intro hx
      apply fb
      intro r
      have rl : (⟨q.val - n, by omega⟩ : Fin (n + n + K)).val < n := by simp only; omega
      simp only [fnet, fpre, rl, ite_true, ind]
      split
      · rename_i h
        simp at h
        rcases h with h | h
        · have : r = ⟨q.val - n, by omega⟩ := Fin.ext h
          rw [this]; omega
        · have : r = q := Fin.ext (by omega)
          rw [this, mq]; exact Nat.le_refl 1
      · exact Nat.zero_le _
  · simp only [q1, q2, dite_false, ind] at hq
    split at hq <;> omega

/-- **Free choice does not help.**  For `0 < n`, the strict free-choice net
built from `G` preserves exactly when `G` is unsatisfiable. -/
theorem fc_preserves_iff_unsatisfiable (G : CNF n K) (hn : 0 < n) :
    Preserves (fnet G) fcap ↔ ¬ Satisfiable G :=
  ⟨fun p s => satisfiable_not_preserves G hn s p,
   fun ns => Classical.byContradiction fun np => ns (not_preserves_satisfiable G np)⟩

end FreeChoice

end CBMDPetriCapacity
