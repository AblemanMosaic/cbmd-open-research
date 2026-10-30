import CBMDFixedState.Realise

/-!
# A verified pseudo-polynomial residue decider

The residue-witness condition on the star asks for a set `P` of senders, missing
at least one, such that every sender outside `P` overflows on top of
`(Σ_P a) mod B`.  It depends on `P` only through two numbers: the residue
`ρ = (Σ_P a) mod B` and the smallest bundle outside `P` (capped at `B + 1`;
`B + 2` marks "none").  This module tabulates which pairs `(ρ, μ)` occur, one
sender at a time, in `O(k · B²)` table entries, and proves:

* `spec_iff`: the table is exactly the set of occurring pairs;
* `dpWitness_iff`: the decider answers `true` exactly when a residue witness
  exists;
* `dpFast_eq`: the array-memoised implementation computes the same answer;
* `safe_of_dpFast`: if the decider answers `false`, no capacity-terminal state
  reachable from the start is bad.

Together with `realise_small` and `realise_pair`, this is a verified procedure
that certifies safety exactly when no witness exists; when one exists, a bad
ending is reachable provided the residue-witness conjecture holds.
-/

namespace CBMDFixedState

namespace Star

variable {k : Nat} (a : Fin k → Nat) (B : Nat)

/-- The smallest bundle outside `P` among `l`, capped at `B + 1`; `B + 2` if none. -/
def minU (P : Fin k → Bool) : List (Fin k) → Nat
  | [] => B + 2
  | i :: l => if P i then minU P l else min (min (a i) (B + 1)) (minU P l)

/-- Which (residue, smallest-outside) pairs occur among the senders of `l`. -/
def spec : List (Fin k) → Nat → Nat → Bool
  | [], ρ, μ => decide (ρ = 0 ∧ μ = B + 2)
  | i :: l, ρ, μ =>
      (List.range B).any (fun ρ' => spec l ρ' μ && decide ((ρ' + a i) % B = ρ)) ||
      (List.range (B + 3)).any (fun μ' => spec l ρ μ' && decide (min (min (a i) (B + 1)) μ' = μ))

theorem minU_le (P : Fin k → Bool) : ∀ l : List (Fin k), minU a B P l ≤ B + 2
  | [] => by simp [minU]
  | i :: l => by
    have := minU_le P l
    unfold minU; split <;> omega

theorem minU_none_iff (P : Fin k → Bool) :
    ∀ l : List (Fin k), minU a B P l = B + 2 ↔ ∀ i ∈ l, P i = true
  | [] => by simp [minU]
  | i :: l => by
    have ih := minU_none_iff P l
    have := minU_le a B P l
    unfold minU
    cases hp : P i
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, forall_eq_or_imp, hp, false_and,
        iff_false]
      omega
    · simp [hp, ih]

theorem minU_block (P : Fin k → Bool) (ρ : Nat) :
    ∀ l : List (Fin k), (B < ρ + minU a B P l ↔ ∀ i ∈ l, P i = false → B < ρ + a i)
  | [] => by simp [minU]; omega
  | i :: l => by
    have ih := minU_block P ρ l
    unfold minU
    cases hp : P i
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons, forall_eq_or_imp, hp, true_implies]
      rw [← ih]
      constructor
      · intro h; constructor <;> omega
      · intro h; omega
    · simp [hp, ih]

theorem lsum_filter_update_true (P : Fin k → Bool) (i : Fin k) :
    ∀ l : List (Fin k), i ∉ l →
      lsum a (l.filter (fun j => if j = i then true else P j)) = lsum a (l.filter P)
  | [], _ => rfl
  | x :: l, h => by
    have hx : x ≠ i := fun e => h (e ▸ List.mem_cons_self)
    have := lsum_filter_update_true P i l (fun m => h (List.mem_cons_of_mem _ m))
    cases hp : P x <;> simp [hx, hp] <;> simpa using this

theorem lsum_filter_update_false (P : Fin k → Bool) (i : Fin k) :
    ∀ l : List (Fin k), i ∉ l →
      lsum a (l.filter (fun j => if j = i then false else P j)) = lsum a (l.filter P)
  | [], _ => rfl
  | x :: l, h => by
    have hx : x ≠ i := fun e => h (e ▸ List.mem_cons_self)
    have := lsum_filter_update_false P i l (fun m => h (List.mem_cons_of_mem _ m))
    cases hp : P x <;> simp [hx, hp] <;> simpa using this

theorem minU_update (P : Fin k → Bool) (i : Fin k) (b : Bool) :
    ∀ l : List (Fin k), i ∉ l → minU a B (fun j => if j = i then b else P j) l = minU a B P l
  | [], _ => rfl
  | x :: l, h => by
    have hx : x ≠ i := fun e => h (e ▸ List.mem_cons_self)
    have := minU_update P i b l (fun m => h (List.mem_cons_of_mem _ m))
    simp [minU, hx, this]

/-- **The table is exactly the set of occurring pairs.** -/
theorem spec_iff (Bpos : 0 < B) : ∀ l : List (Fin k), l.Nodup → ∀ ρ μ,
    spec a B l ρ μ = true ↔
      ∃ P : Fin k → Bool, lsum a (l.filter P) % B = ρ ∧ minU a B P l = μ
  | [], _, ρ, μ => by
    simp only [spec, decide_eq_true_eq, List.filter_nil, lsum_nil, Nat.zero_mod, minU]
    constructor
    · intro ⟨h1, h2⟩; exact ⟨fun _ => true, h1.symm, h2.symm⟩
    · intro ⟨_, h1, h2⟩; exact ⟨h1.symm, h2.symm⟩
  | i :: l, nd, ρ, μ => by
    have hi : i ∉ l := (List.nodup_cons.mp nd).1
    have nd' : l.Nodup := (List.nodup_cons.mp nd).2
    have ih := spec_iff Bpos l nd'
    simp only [spec, Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · rintro (⟨ρ', _, hs, he⟩ | ⟨μ', _, hs, he⟩)
      · obtain ⟨P, h1, h2⟩ := (ih ρ' μ).mp hs
        refine ⟨fun j => if j = i then true else P j, ?_, ?_⟩
        · simp only [List.filter_cons, ↓reduceIte, lsum_cons]
          rw [lsum_filter_update_true a P i l hi, ← he, ← h1, Nat.add_comm]
          exact (Nat.mod_add_mod _ _ _).symm
        · simp only [minU, ↓reduceIte]
          rw [minU_update a B P i true l hi, h2]
      · obtain ⟨P, h1, h2⟩ := (ih ρ μ').mp hs
        refine ⟨fun j => if j = i then false else P j, ?_, ?_⟩
        · simp only [List.filter_cons, ↓reduceIte, Bool.false_eq_true]
          rw [lsum_filter_update_false a P i l hi, h1]
        · simp only [minU, ↓reduceIte, Bool.false_eq_true]
          rw [minU_update a B P i false l hi, h2, he]
    · rintro ⟨P, h1, h2⟩
      cases hp : P i
      · right
        refine ⟨minU a B P l, by have := minU_le a B P l; omega, (ih ρ _).mpr ⟨P, ?_, rfl⟩, ?_⟩
        · simpa [List.filter_cons, hp] using h1
        · simpa [minU, hp] using h2
      · left
        refine ⟨lsum a (l.filter P) % B, Nat.mod_lt _ Bpos, (ih _ μ).mpr ⟨P, rfl, ?_⟩, ?_⟩
        · simpa [minU, hp] using h2
        · simp only [List.filter_cons, hp, ↓reduceIte, lsum_cons] at h1
          rw [← h1, Nat.mod_add_mod, Nat.add_comm]

/-- The decider: some occurring pair has a sender outside and blocks it. -/
def dpWitness : Bool :=
  (List.range B).any (fun ρ => (List.range (B + 2)).any (fun μ =>
    spec a B (List.finRange k) ρ μ && decide (B < ρ + μ)))

/-- A residue witness, as a predicate. -/
def WitnessP (P : Fin k → Bool) : Prop :=
  (∃ i, P i = false) ∧ ∀ i, P i = false → B < ps a P % B + a i

/-- **The decider is exact for the witness condition.** -/
theorem dpWitness_iff (Bpos : 0 < B) : dpWitness a B = true ↔ ∃ P, WitnessP a B P := by
  have nd := List.nodup_finRange k
  simp only [dpWitness, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ρ, hρ, μ, hμ, hs, hb⟩
    obtain ⟨P, h1, h2⟩ := (spec_iff a B Bpos _ nd ρ μ).mp hs
    refine ⟨P, ?_, ?_⟩
    · apply Classical.byContradiction
      intro hn
      have : ∀ i ∈ List.finRange k, P i = true := fun i _ => by
        cases hp : P i
        · exact absurd ⟨i, hp⟩ hn
        · rfl
      have := (minU_none_iff a B P _).mpr this
      omega
    · intro i hi
      have hblk := (minU_block a B P ρ _).mp (by rw [h2]; exact hb) i (List.mem_finRange i) hi
      have : ps a P % B = ρ := h1
      omega
  · rintro ⟨P, ⟨i, hi⟩, hblk⟩
    refine ⟨ps a P % B, Nat.mod_lt _ Bpos, minU a B P (List.finRange k), ?_,
      (spec_iff a B Bpos _ nd _ _).mpr ⟨P, rfl, rfl⟩, ?_⟩
    · have hne : minU a B P (List.finRange k) ≠ B + 2 := by
        intro h
        have := (minU_none_iff a B P _).mp h i (List.mem_finRange i)
        rw [hi] at this; cases this
      have := minU_le a B P (List.finRange k)
      omega
    · exact (minU_block a B P _ _).mpr (fun j _ hj => hblk j hj)

/-! ## The memoised implementation -/

theorem any_congr_mem {α : Type} {p q : α → Bool} : ∀ {l : List α}, (∀ x ∈ l, p x = q x) →
    l.any p = l.any q
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.any_cons]
    rw [h x List.mem_cons_self, any_congr_mem (fun y hy => h y (List.mem_cons_of_mem _ hy))]

def lookup (t : Array Bool) (ρ μ : Nat) : Bool := t.getD (ρ * (B + 3) + μ) false

def table : List (Fin k) → Array Bool
  | [] => Array.ofFn (n := B * (B + 3)) fun idx =>
      decide (idx.val / (B + 3) = 0 ∧ idx.val % (B + 3) = B + 2)
  | i :: l =>
      let t := table l
      Array.ofFn (n := B * (B + 3)) fun idx =>
        let ρ := idx.val / (B + 3)
        let μ := idx.val % (B + 3)
        (List.range B).any (fun ρ' => lookup B t ρ' μ && decide ((ρ' + a i) % B = ρ)) ||
        (List.range (B + 3)).any (fun μ' => lookup B t ρ μ' && decide (min (min (a i) (B + 1)) μ' = μ))

theorem idx_div (ρ μ : Nat) (hμ : μ < B + 3) : (ρ * (B + 3) + μ) / (B + 3) = ρ := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hμ, Nat.add_zero]

theorem idx_mod (ρ μ : Nat) (hμ : μ < B + 3) : (ρ * (B + 3) + μ) % (B + 3) = μ := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hμ]

theorem idx_lt (ρ μ : Nat) (hρ : ρ < B) (hμ : μ < B + 3) : ρ * (B + 3) + μ < B * (B + 3) := by
  have : (ρ + 1) * (B + 3) ≤ B * (B + 3) := Nat.mul_le_mul_right _ hρ
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem lookup_ofFn (f : Fin (B * (B + 3)) → Bool) (ρ μ : Nat) (hρ : ρ < B) (hμ : μ < B + 3) :
    lookup B (Array.ofFn f) ρ μ = f ⟨ρ * (B + 3) + μ, idx_lt B ρ μ hρ hμ⟩ := by
  simp only [lookup, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  rw [dite_eq_left_of_eq_true (eq_true (idx_lt B ρ μ hρ hμ))]
  rfl

/-- **The memoised table agrees with the specification** on its whole domain. -/
theorem table_eq : ∀ (l : List (Fin k)) (ρ μ : Nat), ρ < B → μ < B + 3 →
    lookup B (table a B l) ρ μ = spec a B l ρ μ
  | [], ρ, μ, hρ, hμ => by
    simp only [table]
    rw [lookup_ofFn B _ ρ μ hρ hμ]
    simp only [idx_div B ρ μ hμ, idx_mod B ρ μ hμ, spec]
  | i :: l, ρ, μ, hρ, hμ => by
    simp only [table]
    rw [lookup_ofFn B _ ρ μ hρ hμ]
    simp only [idx_div B ρ μ hμ, idx_mod B ρ μ hμ, spec]
    congr 1
    · apply any_congr_mem
      intro ρ' hρ'
      rw [table_eq l ρ' μ (List.mem_range.mp hρ') hμ]
    · apply any_congr_mem
      intro μ' hμ'
      rw [table_eq l ρ μ' hρ (List.mem_range.mp hμ')]

def dpFast : Bool :=
  let t := table a B (List.finRange k)
  (List.range B).any (fun ρ => (List.range (B + 2)).any (fun μ =>
    lookup B t ρ μ && decide (B < ρ + μ)))

theorem dpFast_eq : dpFast a B = dpWitness a B := by
  simp only [dpFast, dpWitness]
  apply any_congr_mem
  intro ρ hρ
  apply any_congr_mem
  intro μ hμ
  rw [table_eq a B _ ρ μ (List.mem_range.mp hρ) (by have := List.mem_range.mp hμ; omega)]

/-! ## Soundness for the star -/

theorem lsum_eq_ps : ∀ L : List (Fin k), L.Nodup → lsum a L = ps a (fun i => decide (i ∈ L))
  | [], _ => by rw [ps_zero a _ (fun i => by simp)]; rfl
  | x :: L, nd => by
    have hx : x ∉ L := (List.nodup_cons.mp nd).1
    have ih := lsum_eq_ps L (List.nodup_cons.mp nd).2
    have ins := ps_insert a (fun i => decide (i ∈ L)) x (by simp [hx])
    rw [lsum_cons, ih]
    rw [show ps a (fun i => decide (i ∈ x :: L)) =
        ps a (fun i => decide (i ∈ L) || decide (i = x)) from
      ps_congr a (fun i => by simp [List.mem_cons, Bool.or_comm]), ins]
    omega

/-- A stuck run yields a predicate witness. -/
theorem stuck_imp_witnessP (h : Stuck a B) : ∃ P, WitnessP a B P := by
  obtain ⟨L, f, run, fB, ⟨i, hi⟩, stuck⟩ := h
  refine ⟨fun j => decide (j ∈ L), ⟨i, by simp [hi]⟩, ?_⟩
  intro j hj
  have hjL : j ∉ L := by simpa using hj
  rw [← lsum_eq_ps a L (run_nodup a B run), fill_eq_mod a B run fB]
  exact stuck j hjL

/-- **Verified safety certificate.**  If the memoised decider answers `false`,
no capacity-terminal state reachable from the start is bad. -/
theorem safe_of_dpFast (apos : ∀ i, 0 < a i) (Bpos : 0 < B) (h : dpFast a B = false) :
    ¬ ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  intro hy
  have st : Stuck a B := (bad_terminal_reachable_iff a B apos).mp hy
  have := (dpWitness_iff a B Bpos).mpr (stuck_imp_witnessP a B st)
  rw [← dpFast_eq] at this
  rw [h] at this
  cases this

/-! ## A kernel-checked instance -/

/-- Bundles given as a list. -/
def bundles (l : List Nat) : Fin l.length → Nat := fun i => l[i]

/-- **The star with bundles `2, 3, 3` and `B = 5` never ends badly**, certified by
the decider evaluated in the kernel. -/
theorem safe_2_3_3 :
    ¬ ∃ y, Reaches (Step (bundles [2, 3, 3]) 5) (stateOf (bundles [2, 3, 3]) [] 0) y ∧
        CapacityTerminal (mult (bundles [2, 3, 3])) (out (bundles [2, 3, 3]) 5)
          (cap (bundles [2, 3, 3]) 5) y ∧
        ¬ OrdinaryStable (out (bundles [2, 3, 3]) 5) y :=
  safe_of_dpFast (bundles [2, 3, 3]) 5 (by decide) (by decide) (by decide)

end Star

end CBMDFixedState
