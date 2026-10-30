import CBMDPetriCapacity.FreeChoice

/-!
# Two consumers per place already suffice for hardness

`FreeChoice.lean` puts all the conflict on one place `g` with many consumers.
`ConflictFree.lean` shows one consumer per place (with input places everywhere)
is polynomial.  This module closes the gap in the other parameter: hardness
holds already when **every place has at most two consumers**, the net is strict
free-choice, all capacities are `1`, and every transition has one or two input
places.

`g` is split into copies `g_0, …, g_{L-1}`, `L = n + K`, one per transition that
used to read `g`, and a cyclic chain of **copier** transitions `g_j → g_{j+1 mod L}`
forces them to agree: a copier is enabled as soon as its input holds, and it can
only be blocked by its output already holding.  So in any bad marking one copy
holding forces every copy to hold.  Each copy is read by its user and by one
copier: two consumers.

Places `Fin (n+n+L)`: `x_i` at `i`, `x̄_i` at `n+i`, `g_j` at `n+n+j`.
Transitions `Fin (n+L+L)`: the variable transition `x_i, x̄_i → ∅` at `i`; the
user of `g_j` at `n+j` (for `j < n` it produces `x_j, x̄_j`, for `j = n+k` the
literal places of clause `k`); the copier `g_j → g_{(j+1) % L}` at `n+L+j`.
`2 ≤ n + K` is assumed so that no copier is a self-loop.
-/

namespace CBMDPetriCapacity

namespace DegreeTwo

open Reduction FreeChoice

variable {n K : Nat}

def dpre (c : Fin (n + (n + K) + (n + K))) (q : Fin (n + n + (n + K))) : Nat :=
  if c.val < n then ind (decide (q.val = c.val) || decide (q.val = n + c.val))
  else if c.val < n + (n + K) then ind (decide (q.val = n + n + (c.val - n)))
  else ind (decide (q.val = n + n + (c.val - n - (n + K))))

def dpost (G : CNF n K) (c : Fin (n + (n + K) + (n + K))) (q : Fin (n + n + (n + K))) : Nat :=
  if h1 : c.val < n then 0
  else if h2 : c.val < n + n then
    ind (decide (q.val = c.val - n) || decide (q.val = n + (c.val - n)))
  else if hc : c.val < n + (n + K) then
    if hq : q.val < n then ind (G.pos ⟨c.val - n - n, by omega⟩ ⟨q.val, hq⟩)
    else if hq' : q.val < n + n then ind (G.neg ⟨c.val - n - n, by omega⟩ ⟨q.val - n, by omega⟩)
    else 0
  else ind (decide (q.val = n + n + ((c.val - n - (n + K) + 1) % (n + K))))

def dnet (G : CNF n K) : Net (n + n + (n + K)) (n + (n + K) + (n + K)) := ⟨dpre, dpost G⟩

def dcap : Fin (n + n + (n + K)) → Nat := fun _ => 1

/-- Who consumes what: the variable transitions read `x_i, x̄_i`; the user of
`g_j` and the copier from `g_j` read `g_j`. -/
theorem consumer_shape (G : CNF n K) (q : Fin (n + n + (n + K))) (x : Fin (n + (n + K) + (n + K)))
    (hx : 0 < (dnet G).pre x q) :
    (q.val < n + n ∧ x.val < n ∧ (q.val = x.val ∨ q.val = n + x.val)) ∨
    (n + n ≤ q.val ∧ n ≤ x.val ∧ x.val < n + (n + K) ∧ x.val = q.val - n) ∨
    (n + n ≤ q.val ∧ n + (n + K) ≤ x.val ∧ x.val = q.val + K) := by
  simp only [dnet, dpre] at hx
  by_cases a : x.val < n
  · simp only [a, ite_true, ind] at hx
    left
    refine ⟨?_, a, ?_⟩ <;> (split at hx <;> simp_all <;> omega)
  · by_cases b : x.val < n + (n + K)
    · simp only [a, b, ite_true, ite_false, ind] at hx
      right; left
      split at hx
      · rename_i h; simp at h; omega
      · simp at hx
    · simp only [a, b, ite_false, ind] at hx
      right; right
      split at hx
      · rename_i h; simp at h; omega
      · simp at hx

/-- Every place has at most two consumers. -/
theorem at_most_two_consumers (G : CNF n K) (q : Fin (n + n + (n + K)))
    (a b c : Fin (n + (n + K) + (n + K)))
    (ha : 0 < (dnet G).pre a q) (hb : 0 < (dnet G).pre b q) (hc : 0 < (dnet G).pre c q) :
    a = b ∨ a = c ∨ b = c := by
  have ka := consumer_shape G q a ha
  have kb := consumer_shape G q b hb
  have kc := consumer_shape G q c hc
  by_cases e1 : a.val = b.val
  · exact Or.inl (Fin.ext e1)
  by_cases e2 : a.val = c.val
  · exact Or.inr (Or.inl (Fin.ext e2))
  · right; right; apply Fin.ext; omega

/-- Strict free choice: a place shared by two distinct transitions is the only
input place of each. -/
theorem free_choice (G : CNF n K) (t t' : Fin (n + (n + K) + (n + K))) (q : Fin (n + n + (n + K)))
    (ht : 0 < (dnet G).pre t q) (ht' : 0 < (dnet G).pre t' q) (ne : t ≠ t') :
    ∀ r, 0 < (dnet G).pre t r → r = q := by
  intro r hr
  have kt := consumer_shape G q t ht
  have kt' := consumer_shape G q t' ht'
  have kr := consumer_shape G r t hr
  have nv : t.val ≠ t'.val := fun h => ne (Fin.ext h)
  apply Fin.ext
  omega

/-- The marking of an assignment, with every copy of `g` holding. -/
def dmark (σ : Fin n → Bool) (q : Fin (n + n + (n + K))) : Nat :=
  if h : q.val < n then ind (σ ⟨q.val, h⟩)
  else if h' : q.val < n + n then ind (!σ ⟨q.val - n, by omega⟩)
  else 1

theorem dmark_admissible (σ : Fin n → Bool) : Admissible dcap (dmark (K := K) σ) := by
  intro q
  simp only [dmark, dcap]
  split
  · exact ind_le _
  split
  · exact ind_le _
  · exact Nat.le_refl _

theorem satisfiable_not_preserves (G : CNF n K) (hL : 2 ≤ n + K) (sat : Satisfiable G) :
    ¬ Preserves (dnet G) dcap := by
  obtain ⟨σ, hs⟩ := sat
  intro pres
  have dead : CapDead (dnet G) dcap (dmark σ) := by
    intro t ⟨ord, fits⟩
    by_cases a : t.val < n
    · have h1 := ord ⟨t.val, by omega⟩
      have h2 := ord ⟨n + t.val, by omega⟩
      have e1 : ¬ n + t.val < n := by omega
      have e2 : n + t.val < n + n := by omega
      have e3 : n + t.val - n = t.val := by omega
      simp only [dnet, dpre, dmark, a, e1, e2, e3, ite_true, dite_true, dite_false,
        decide_true, Bool.true_or, Bool.or_true, ind] at h1 h2
      cases hσ : σ ⟨t.val, a⟩ <;> simp_all
    by_cases b : t.val < n + n
    · have hi : t.val - n < n := by omega
      cases hσ : σ ⟨t.val - n, hi⟩
      · have h := fits ⟨n + (t.val - n), by omega⟩
        have e1 : ¬ n + (t.val - n) < n := by omega
        have e2 : n + (t.val - n) < n + n := by omega
        have e3 : n + (t.val - n) - n = t.val - n := by omega
        have bL : t.val < n + (n + K) := by omega
        simp only [dnet, dpre, dpost, dcap, dmark, a, b, bL, e1, e2, e3, ite_true, ite_false,
          dite_true, dite_false, ind, hσ] at h
        simp [show n ≠ 0 by omega] at h; all_goals omega
      · have h := fits ⟨t.val - n, by omega⟩
        have bL : t.val < n + (n + K) := by omega
        simp only [dnet, dpre, dpost, dcap, dmark, a, b, bL, hi, ite_true, ite_false,
          dite_true, ind, hσ] at h
        simp [show n ≠ 0 by omega] at h; all_goals omega
    by_cases c : t.val < n + (n + K)
    · have hk : t.val - n - n < K := by omega
      obtain ⟨x, hx⟩ := hs ⟨t.val - n - n, hk⟩
      rcases hx with ⟨hneg, hv⟩ | ⟨hpos, hv⟩
      · have h := fits ⟨n + x.val, by omega⟩
        have e1 : ¬ n + x.val < n := by omega
        have e2 : n + x.val < n + n := by omega
        have ex : (⟨n + x.val - n, by omega⟩ : Fin n) = x := Fin.ext (by simp)
        simp only [dnet, dpre, dpost, dcap, dmark, a, b, c, e1, e2, ex, ite_true, ite_false,
          dite_true, dite_false, hneg, hv, ind] at h
        have hne : ¬ (n + x.val = n + n + (t.val - n)) := by have := x.isLt; omega
        simp [hne] at h
      · have h := fits ⟨x.val, by omega⟩
        simp only [dnet, dpre, dpost, dcap, dmark, a, b, c, x.isLt, ite_true, ite_false,
          dite_true, dite_false, hpos, hv, ind] at h
        have hne : ¬ (x.val = n + n + (t.val - n)) := by have := x.isLt; omega
        simp [hne] at h
    · -- a copier: its output copy already holds
      have hj : t.val - n - (n + K) < n + K := by omega
      have hm := Nat.mod_lt (t.val - n - (n + K) + 1) (by omega : 0 < n + K)
      have h := fits ⟨n + n + ((t.val - n - (n + K) + 1) % (n + K)), by omega⟩
      have ne : (t.val - n - (n + K) + 1) % (n + K) ≠ t.val - n - (n + K) := by
        intro e
        by_cases w : t.val - n - (n + K) + 1 < n + K
        · rw [Nat.mod_eq_of_lt w] at e; omega
        · have : t.val - n - (n + K) + 1 = n + K := by omega
          rw [this, Nat.mod_self] at e; omega
      have g1 : ¬ n + n + ((t.val - n - (n + K) + 1) % (n + K)) < n := by omega
      have g2 : ¬ n + n + ((t.val - n - (n + K) + 1) % (n + K)) < n + n := by omega
      simp only [dnet, dpre, dpost, dcap, dmark, a, b, c, g1, g2, ite_false, dite_false,
        decide_true, ind, ite_true] at h
      simp [ne] at h
  apply pres (dmark σ) (dmark_admissible σ) dead ⟨n, by omega⟩
  intro q
  have a : ¬ n < n := Nat.lt_irrefl n
  have b : n < n + (n + K) := by omega
  simp only [dnet, dpre, a, b, ite_false, ite_true, ind]
  split
  · rename_i h
    simp at h
    have g1 : ¬ q.val < n := by omega
    have g2 : ¬ q.val < n + n := by omega
    simp [dmark, g1, g2]
  · exact Nat.zero_le _

/-- At a capacity-dead marking an ordinarily enabled transition overflows somewhere. -/
theorem overflow_of_dead (G : CNF n K) {m : Marking (n + n + (n + K))}
    (dead : CapDead (dnet G) dcap m) {c : Fin (n + (n + K) + (n + K))}
    (oc : OrdEnabled (dnet G) m c) :
    ∃ q, ¬ (m q - (dnet G).pre c q + (dnet G).post c q ≤ dcap q) :=
  Classical.byContradiction fun h =>
    dead c ⟨oc, fun q => Classical.byContradiction fun hq => h ⟨q, hq⟩⟩

theorem satisfiable_of_bad (G : CNF n K) (hL : 2 ≤ n + K) {m : Marking (n + n + (n + K))}
    (adm : Admissible dcap m) (dead : CapDead (dnet G) dcap m)
    {t : Fin (n + (n + K) + (n + K))} (ord : OrdEnabled (dnet G) m t) : Satisfiable G := by
  have le1 : ∀ q, m q ≤ 1 := adm
  -- variable transitions have no outputs, so they are never enabled at a dead marking
  have var_blocked : ∀ i : Fin (n + (n + K) + (n + K)), i.val < n → ¬ OrdEnabled (dnet G) m i := by
    intro i hi o
    apply dead i
    refine ⟨o, fun q => ?_⟩
    simp only [dnet, dpost, hi, dite_true, Nat.add_zero]
    exact Nat.le_trans (Nat.sub_le _ _) (le1 q)
  have tn : ¬ t.val < n := fun h => var_blocked t h ord
  -- a copy of g holds
  have ⟨j0, hj0, mj0⟩ : ∃ j, ∃ _ : j < n + K, 1 ≤ m ⟨n + n + j, by omega⟩ := by
    by_cases b : t.val < n + (n + K)
    · refine ⟨t.val - n, by omega, ?_⟩
      have := ord ⟨n + n + (t.val - n), by omega⟩
      simp only [dnet, dpre, tn, b, ite_false, ite_true, ind, decide_true] at this
      exact this
    · refine ⟨t.val - n - (n + K), by omega, ?_⟩
      have := ord ⟨n + n + (t.val - n - (n + K)), by omega⟩
      simp only [dnet, dpre, tn, b, ite_false, ind, decide_true] at this
      exact this
  -- the copier chain passes it on
  have pass : ∀ j (hj : j < n + K), 1 ≤ m ⟨n + n + j, by omega⟩ →
      1 ≤ m ⟨n + n + (j + 1) % (n + K), by have := Nat.mod_lt (j + 1) (by omega : 0 < n + K); omega⟩ := by
    intro j hj mj
    let c : Fin (n + (n + K) + (n + K)) := ⟨n + (n + K) + j, by omega⟩
    have c1 : ¬ c.val < n := by simp only [c]; omega
    have c2 : ¬ c.val < n + (n + K) := by simp only [c]; omega
    have c3 : ¬ c.val < n + n := by simp only [c]; omega
    have cj : c.val - n - (n + K) = j := by simp only [c]; omega
    have oc : OrdEnabled (dnet G) m c := by
      intro r
      simp only [dnet, dpre, c1, c2, ite_false, ind, cj]
      split
      · rename_i h
        simp only [decide_eq_true_eq] at h
        have : r = ⟨n + n + j, by omega⟩ := Fin.ext h
        rw [this]; exact mj
      · exact Nat.zero_le _
    obtain ⟨q, hq⟩ := overflow_of_dead G dead oc
    have mle := le1 q
    have hmod := Nat.mod_lt (j + 1) (by omega : 0 < n + K)
    have ne : (j + 1) % (n + K) ≠ j := by
      intro e
      by_cases w : j + 1 < n + K
      · rw [Nat.mod_eq_of_lt w] at e; omega
      · have : j + 1 = n + K := by omega
        rw [this, Nat.mod_self] at e; omega
    simp only [dnet, dpre, dpost, dcap, c1, c2, c3, ite_false, dite_false, ind, cj] at hq
    by_cases hq1 : q.val = n + n + (j + 1) % (n + K)
    · have hq2 : ¬ q.val = n + n + j := by omega
      simp only [hq1, hq2, decide_true, decide_false, ite_true, ite_false, Nat.sub_zero] at hq
      have : q = ⟨n + n + (j + 1) % (n + K), by omega⟩ := Fin.ext hq1
      rw [← this]; omega
    · have hq1' : ¬ (decide (q.val = n + n + (j + 1) % (n + K)) = true) := by simp [hq1]
      rw [if_neg hq1'] at hq
      split at hq <;> omega
  have all_g : ∀ j, (h : j < n + K) → 1 ≤ m ⟨n + n + j, by omega⟩ := by
    have step : ∀ k, 1 ≤ m ⟨n + n + (j0 + k) % (n + K),
        by have := Nat.mod_lt (j0 + k) (by omega : 0 < n + K); omega⟩ := by
      intro k
      induction k with
      | zero =>
        have e : (j0 + 0) % (n + K) = j0 := by rw [Nat.add_zero, Nat.mod_eq_of_lt hj0]
        have : (⟨n + n + (j0 + 0) % (n + K), by omega⟩ : Fin (n + n + (n + K))) =
            ⟨n + n + j0, by omega⟩ := Fin.ext (by simp only [e])
        rw [this]; exact mj0
      | succ k ih =>
        have hm := Nat.mod_lt (j0 + k) (by omega : 0 < n + K)
        have := pass ((j0 + k) % (n + K)) hm ih
        have e : ((j0 + k) % (n + K) + 1) % (n + K) = (j0 + (k + 1)) % (n + K) := by
          rw [Nat.mod_add_mod, Nat.add_assoc]
        have : (⟨n + n + ((j0 + k) % (n + K) + 1) % (n + K), by
            have := Nat.mod_lt ((j0 + k) % (n + K) + 1) (by omega : 0 < n + K); omega⟩ :
              Fin (n + n + (n + K))) = ⟨n + n + (j0 + (k + 1)) % (n + K), by
            have := Nat.mod_lt (j0 + (k + 1)) (by omega : 0 < n + K); omega⟩ :=
          Fin.ext (by simp only [e])
        rw [← this]; exact this ▸ (pass ((j0 + k) % (n + K)) hm ih)
    intro j hj
    have e : (j0 + (j + (n + K) - j0)) % (n + K) = j := by
      have : j0 + (j + (n + K) - j0) = j + (n + K) := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
    have := step (j + (n + K) - j0)
    have h' : (⟨n + n + (j0 + (j + (n + K) - j0)) % (n + K), by
        have := Nat.mod_lt (j0 + (j + (n + K) - j0)) (by omega : 0 < n + K); omega⟩ :
          Fin (n + n + (n + K))) = ⟨n + n + j, by omega⟩ := Fin.ext (by simp only [e])
    rw [h'] at this; exact this
  refine ⟨fun a => decide (0 < m ⟨a.val, by omega⟩), fun k => ?_⟩
  -- the user of g_{n+k} is clause k's transition; it is enabled, so it overflows
  let c : Fin (n + (n + K) + (n + K)) := ⟨n + n + k.val, by omega⟩
  have c1 : ¬ c.val < n := by simp only [c]; omega
  have c3 : ¬ c.val < n + n := by simp only [c]; omega
  have c2 : c.val < n + (n + K) := by simp only [c]; omega
  have ck : (⟨c.val - n - n, by simp only [c]; omega⟩ : Fin K) = k := Fin.ext (by simp only [c]; omega)
  have oc : OrdEnabled (dnet G) m c := by
    intro r
    simp only [dnet, dpre, c1, c2, ite_false, ite_true, ind]
    split
    · rename_i h
      simp only [decide_eq_true_eq] at h
      have hcv : c.val - n = n + k.val := by show n + n + k.val - n = n + k.val; omega
      rw [hcv] at h
      have := all_g (n + k.val) (by omega)
      have e : r = ⟨n + n + (n + k.val), by omega⟩ := Fin.ext h
      rw [e]; exact this
    · exact Nat.zero_le _
  obtain ⟨q, hq⟩ := overflow_of_dead G dead oc
  have mle := le1 q
  simp only [dnet, dpre, dpost, dcap, c1, c2, c3, ite_false, ite_true, dite_false, dite_true, ck] at hq
  by_cases q1 : q.val < n
  · have hp0 : ¬ (decide (q.val = n + n + (c.val - n)) = true) := by
      simp only [decide_eq_true_eq, c]; omega
    simp only [q1, dite_true, ind, hp0, ite_false, Nat.sub_zero] at hq
    cases hp : G.pos k ⟨q.val, q1⟩
    · simp [hp] at hq; all_goals omega
    · refine ⟨⟨q.val, q1⟩, Or.inr ⟨hp, ?_⟩⟩
      simp [hp] at hq
      simp only [decide_eq_true_eq]
      have e : (⟨q.val, by omega⟩ : Fin (n + n + (n + K))) = q := Fin.ext rfl
      rw [e]; omega
  by_cases q2 : q.val < n + n
  · have hp0 : ¬ (decide (q.val = n + n + (c.val - n)) = true) := by
      simp only [decide_eq_true_eq, c]; omega
    simp only [q1, q2, dite_true, dite_false, ind, hp0, ite_false, Nat.sub_zero] at hq
    cases hneg : G.neg k ⟨q.val - n, by omega⟩
    · simp [hneg] at hq; all_goals omega
    · refine ⟨⟨q.val - n, by omega⟩, Or.inl ⟨hneg, ?_⟩⟩
      simp [hneg] at hq
      have mq : m q = 1 := by omega
      have fb := var_blocked ⟨q.val - n, by omega⟩ (by simp only; omega)
      simp only [decide_eq_false_iff_not, Nat.not_lt, Nat.le_zero]
      apply Classical.byContradiction
      intro hx
      apply fb
      intro r
      have rl : (⟨q.val - n, by omega⟩ : Fin (n + (n + K) + (n + K))).val < n := by simp only; omega
      simp only [dnet, dpre, rl, ite_true, ind]
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

/-- **Two consumers per place suffice.**  For `2 ≤ n + K`, the strict
free-choice net built from `G`, in which every place has at most two consumers,
preserves exactly when `G` is unsatisfiable. -/
theorem degreeTwo_preserves_iff_unsatisfiable (G : CNF n K) (hL : 2 ≤ n + K) :
    Preserves (dnet G) dcap ↔ ¬ Satisfiable G := by
  constructor
  · exact fun p s => satisfiable_not_preserves G hL s p
  · intro ns m adm dead t ord
    exact ns (satisfiable_of_bad G hL adm dead ord)

end DegreeTwo

end CBMDPetriCapacity
