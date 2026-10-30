import CBMDPetriCapacity.ConflictFree
import CBMDPetriCapacity.Guard

/-!
# Input-less transitions make conflict-free nets hard

`ConflictFree.lean` decides preservation for conflict-free nets **in which
every transition has an input place**.  This module shows the hypothesis is
not a convenience: with input-less transitions allowed, conflict-free nets are
already as hard as the general problem.

For a CNF `G` on `n` atoms with `K` clauses: places `x⁺_i` (at `i`) and
`x⁻_i` (at `n+i`), all of capacity `1`; transitions `Fin (n+K)`:

| index | inputs | outputs | blocked exactly when |
|---|---|---|---|
| `i`   | `x⁺_i, x⁻_i` | — | not both hold |
| `n+k` | — | `x⁺_a` for `a ∈ k`, `x⁻_a` for `¬a ∈ k` | some literal place of clause `k` holds |

Each place is consumed only by its variable's transition, so the net is
conflict-free.  A capacity-dead marking is exactly a consistent partial
assignment satisfying every clause; the clause transitions, having no inputs,
are always ordinarily enabled.  So for `0 < K`, the net preserves exactly when
`G` is unsatisfiable.
-/

namespace CBMDPetriCapacity

namespace InputLess

open Reduction ConflictFree

variable {n K : Nat}

def ipre (c : Fin (n + K)) (q : Fin (n + n)) : Nat :=
  if c.val < n then ind (decide (q.val = c.val) || decide (q.val = n + c.val)) else 0

def ipost (G : CNF n K) (c : Fin (n + K)) (q : Fin (n + n)) : Nat :=
  if hc : c.val < n then 0
  else if hq : q.val < n then ind (G.pos ⟨c.val - n, by omega⟩ ⟨q.val, hq⟩)
  else ind (G.neg ⟨c.val - n, by omega⟩ ⟨q.val - n, by omega⟩)

def inet (G : CNF n K) : Net (n + n) (n + K) := ⟨ipre, ipost G⟩

def icap : Fin (n + n) → Nat := fun _ => 1

theorem inet_conflictFree (G : CNF n K) : IsConflictFree (inet G) := by
  intro q t t' h h'
  simp only [inet, ipre] at h h'
  split at h <;> split at h' <;> simp_all [ind]
  · split at h <;> split at h' <;> simp_all
    apply Fin.ext; omega

theorem clause_has_no_input (G : CNF n K) (k : Fin K) (q : Fin (n + n)) :
    (inet G).pre ⟨n + k.val, by omega⟩ q = 0 := by
  have : ¬ n + k.val < n := by omega
  simp [inet, ipre, this]

/-- The marking of an assignment: `x⁺_a ↦ σ a`, `x⁻_a ↦ ¬σ a`. -/
def imark (σ : Fin n → Bool) (q : Fin (n + n)) : Nat :=
  if h : q.val < n then ind (σ ⟨q.val, h⟩) else ind (!σ ⟨q.val - n, by omega⟩)

theorem satisfiable_not_preserves (G : CNF n K) (hK : 0 < K) (sat : Satisfiable G) :
    ¬ Preserves (inet G) icap := by
  obtain ⟨σ, hs⟩ := sat
  intro pres
  have adm : Admissible icap (imark σ) := by
    intro q; simp only [imark, icap]; split <;> (simp only [ind]; split <;> omega)
  have dead : CapDead (inet G) icap (imark σ) := by
    intro t ⟨ord, fits⟩
    by_cases a : t.val < n
    · have h1 := ord ⟨t.val, by omega⟩
      have h2 := ord ⟨n + t.val, by omega⟩
      have e1 : ¬ n + t.val < n := by omega
      have e3 : n + t.val - n = t.val := by omega
      simp only [inet, ipre, imark, a, e1, e3, ite_true, dite_true, dite_false,
        decide_true, Bool.true_or, Bool.or_true, ind] at h1 h2
      cases hσ : σ ⟨t.val, a⟩ <;> simp_all
    · have hk : t.val - n < K := by omega
      obtain ⟨x, hx⟩ := hs ⟨t.val - n, hk⟩
      rcases hx with ⟨hneg, hv⟩ | ⟨hpos, hv⟩
      · have h := fits ⟨n + x.val, by omega⟩
        have e1 : ¬ n + x.val < n := by omega
        have ex : (⟨n + x.val - n, by omega⟩ : Fin n) = x := Fin.ext (by simp)
        simp only [inet, ipre, ipost, imark, icap, a, e1, ex, ite_false, dite_false,
          hneg, hv, ind] at h
        simp at h
      · have h := fits ⟨x.val, by omega⟩
        simp only [inet, ipre, ipost, imark, icap, a, x.isLt, ite_false, dite_true, dite_false,
          hpos, hv, ind] at h
        simp at h
  apply pres (imark σ) adm dead ⟨n + 0, by omega⟩
  intro q
  rw [clause_has_no_input G ⟨0, hK⟩ q]
  exact Nat.zero_le _

/-- Any capacity-dead admissible marking already yields a satisfying
assignment; ordinary enabledness is not even needed for this direction. -/
theorem satisfiable_of_capDead (G : CNF n K) {m : Marking (n + n)}
    (adm : Admissible icap m) (dead : CapDead (inet G) icap m) : Satisfiable G := by
  have le1 : ∀ q, m q ≤ 1 := adm
  -- a variable transition is never ordinarily enabled at a dead marking
  have var_blocked : ∀ i : Fin (n + K), i.val < n → ¬ OrdEnabled (inet G) m i := by
    intro i hi o
    apply dead i
    refine ⟨o, fun q => ?_⟩
    simp only [inet, ipost, hi, dite_true, Nat.add_zero]
    exact Nat.le_trans (Nat.sub_le _ _) (le1 q)
  refine ⟨fun a => decide (0 < m ⟨a.val, by omega⟩), fun k => ?_⟩
  let c : Fin (n + K) := ⟨n + k.val, by omega⟩
  have c1 : ¬ c.val < n := by simp only [c]; omega
  have ek : (⟨c.val - n, by simp only [c]; omega⟩ : Fin K) = k := Fin.ext (by simp only [c]; omega)
  have oc : OrdEnabled (inet G) m c := fun q => by
    rw [clause_has_no_input G k q]; exact Nat.zero_le _
  have hex : ∃ q, ¬ (m q - (inet G).pre c q + (inet G).post c q ≤ icap q) :=
    Classical.byContradiction fun h =>
      dead c ⟨oc, fun q => Classical.byContradiction fun hq => h ⟨q, hq⟩⟩
  obtain ⟨q, hq⟩ := hex
  have mle := le1 q
  rw [show (inet G).pre c q = 0 from clause_has_no_input G k q] at hq
  simp only [inet, ipost, icap, c1, dite_false, ek] at hq
  by_cases q1 : q.val < n
  · simp only [q1, dite_true, ind] at hq
    cases hp : G.pos k ⟨q.val, q1⟩
    · simp [hp] at hq; all_goals omega
    · refine ⟨⟨q.val, q1⟩, Or.inr ⟨hp, ?_⟩⟩
      simp [hp] at hq
      simp only [decide_eq_true_eq]
      have e : (⟨q.val, by omega⟩ : Fin (n + n)) = q := Fin.ext rfl
      rw [e]; omega
  · simp only [q1, dite_false, ind] at hq
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
      have rl : (⟨q.val - n, by omega⟩ : Fin (n + K)).val < n := by simp only; omega
      simp only [inet, ipre, rl, ite_true, ind]
      split
      · rename_i h
        simp at h
        rcases h with h | h
        · have : r = ⟨q.val - n, by omega⟩ := Fin.ext h
          rw [this]; omega
        · have : r = q := Fin.ext (by omega)
          rw [this, mq]; exact Nat.le_refl 1
      · exact Nat.zero_le _

/-- **Input-less transitions make conflict-free nets hard.**  For `0 < K`, the
conflict-free net built from `G` preserves exactly when `G` is unsatisfiable. -/
theorem inputless_preserves_iff_unsatisfiable (G : CNF n K) (hK : 0 < K) :
    Preserves (inet G) icap ↔ ¬ Satisfiable G := by
  constructor
  · exact fun p s => satisfiable_not_preserves G hK s p
  · intro ns m adm dead _ _
    exact ns (satisfiable_of_capDead G adm dead)

end InputLess

end CBMDPetriCapacity
