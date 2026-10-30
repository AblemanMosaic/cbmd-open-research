import CBMDFixedState.Semantics

/-!
# The star: reaching the normal form is exact bin packing

`k` senders each hold one bundle: sender `i` has `a i` chips, outdegree `a i`,
and sends all of them to one receiver `v`.  The receiver has capacity and
outdegree `B` and sends everything to the sink.  Since `v` never holds more
than `B` chips, it can fire only when it holds exactly `B`; a bundle fits only
if it does not push `v` past `B`.

The reachable states are exactly those described by a **bin run** — an order of
the fired senders in which each bundle fits into the current fill, with the
fill reset to `0` whenever it reaches `B` (`reach_iff`).  Consequently the state
with every sender fired is reachable exactly when the bundles can be ordered
without ever crossing a multiple of `B` (`all_fired_reachable_iff`), and a bad
capacity-terminal state is reachable exactly when some run gets stuck
(`bad_terminal_reachable_iff`).
-/

namespace CBMDFixedState

namespace Star

variable {k : Nat} (a : Fin k → Nat) (B : Nat)

def mult (u w : Fin (k + 1)) : Nat :=
  Fin.lastCases 0 (fun i => Fin.lastCases (a i) (fun _ => 0) w) u

def out (u : Fin (k + 1)) : Nat := Fin.lastCases B a u

def cap (u : Fin (k + 1)) : Nat := Fin.lastCases B a u

/-- The state in which the senders in `L` have fired and `v` holds `f`. -/
def stateOf (L : List (Fin k)) (f : Nat) : Chips (k + 1) :=
  fun u => Fin.lastCases f (fun i => if i ∈ L then 0 else a i) u

/-- A bin run: fire a sender whose bundle fits, or empty a full receiver. -/
inductive Run : List (Fin k) → Nat → Prop
  | nil : Run [] 0
  | add {L : List (Fin k)} {f : Nat} (i : Fin k) :
      Run L f → i ∉ L → f + a i ≤ B → Run (L ++ [i]) (f + a i)
  | reset {L : List (Fin k)} : Run L B → Run L 0

abbrev Step := CapacityStep (mult a) (wFire (mult a) (out a B)) (out a B) (cap a B)

theorem run_le {L : List (Fin k)} {f : Nat} (r : Run a B L f) : f ≤ B := by
  induction r with
  | nil => exact Nat.zero_le _
  | add _ _ _ h _ => exact h
  | reset _ _ => exact Nat.zero_le _

@[simp] theorem stateOf_last (L : List (Fin k)) (f : Nat) :
    stateOf a L f (Fin.last k) = f := by simp [stateOf]

@[simp] theorem stateOf_cast (L : List (Fin k)) (f : Nat) (i : Fin k) :
    stateOf a L f i.castSucc = if i ∈ L then 0 else a i := by simp [stateOf]

theorem fire_receiver (L : List (Fin k)) :
    wFire (mult a) (out a B) (stateOf a L B) (Fin.last k) = stateOf a L 0 := by
  funext w
  induction w using Fin.lastCases with
  | last => simp [wFire, out]
  | cast j =>
    have : j.castSucc ≠ Fin.last k := fun h => by have := congrArg Fin.val h; simp at this; omega
    simp [wFire, this, mult]

theorem fire_sender (L : List (Fin k)) (f : Nat) (i : Fin k) (hi : i ∉ L) :
    wFire (mult a) (out a B) (stateOf a L f) i.castSucc = stateOf a (L ++ [i]) (f + a i) := by
  funext w
  induction w using Fin.lastCases with
  | last =>
    have : Fin.last k ≠ i.castSucc := fun h => by have := congrArg Fin.val h; simp at this; omega
    simp [wFire, this, mult]
  | cast j =>
    by_cases e : j = i
    · subst e; simp [wFire, out, hi]
    · have : j.castSucc ≠ i.castSucc := fun h => e (Fin.castSucc_inj.mp h)
      simp [wFire, this, mult, e]

theorem legal_receiver (L : List (Fin k)) :
    CapacityLegal (mult a) (out a B) (cap a B) (stateOf a L B) (Fin.last k) := by
  refine ⟨by simp [OrdinaryUnstable, out], ?_⟩
  intro ⟨w, hw, _⟩
  simp [mult] at hw

theorem legal_sender (L : List (Fin k)) (f : Nat) (i : Fin k) (hi : i ∉ L)
    (fits : f + a i ≤ B) :
    CapacityLegal (mult a) (out a B) (cap a B) (stateOf a L f) i.castSucc := by
  refine ⟨by simp [OrdinaryUnstable, out, hi], ?_⟩
  intro ⟨w, hw, over⟩
  induction w using Fin.lastCases with
  | last => simp [cap, mult] at over; omega
  | cast j => simp [mult] at hw

theorem reach_of_run {L : List (Fin k)} {f : Nat} (r : Run a B L f) :
    Reaches (Step a B) (stateOf a [] 0) (stateOf a L f) := by
  induction r with
  | nil => exact Reaches.refl _
  | add i _ hi fits ih =>
    exact Reaches.tail ih ⟨i.castSucc, legal_sender a B _ _ i hi fits, fire_sender a B _ _ i hi⟩
  | reset _ ih =>
    exact Reaches.tail ih ⟨Fin.last k, legal_receiver a B _, fire_receiver a B _⟩

theorem run_of_reach (apos : ∀ i, 0 < a i) {y : Chips (k + 1)}
    (h : Reaches (Step a B) (stateOf a [] 0) y) : ∃ L f, Run a B L f ∧ y = stateOf a L f := by
  induction h with
  | refl => exact ⟨[], 0, Run.nil, rfl⟩
  | tail _ step ih =>
    obtain ⟨L, f, r, rfl⟩ := ih
    obtain ⟨u, ⟨unst, nb⟩, rfl⟩ := step
    have fle := run_le a B r
    induction u using Fin.lastCases with
    | last =>
      have hf : f = B := by simp [OrdinaryUnstable, out] at unst; omega
      refine ⟨L, 0, Run.reset (hf ▸ r), ?_⟩
      rw [hf]; exact fire_receiver a B L
    | cast i =>
      have hi : i ∉ L := by
        intro m
        simp [OrdinaryUnstable, out, m] at unst
        have := apos i; omega
      have fits : f + a i ≤ B := by
        apply Classical.byContradiction
        intro h
        exact nb ⟨Fin.last k, by simp [mult]; exact apos i, by simp [cap, mult]; omega⟩
      exact ⟨L ++ [i], f + a i, Run.add i r hi fits, fire_sender a B L f i hi⟩

/-- **The reachable states are exactly the bin runs.** -/
theorem reach_iff (apos : ∀ i, 0 < a i) (y : Chips (k + 1)) :
    Reaches (Step a B) (stateOf a [] 0) y ↔ ∃ L f, Run a B L f ∧ y = stateOf a L f :=
  ⟨run_of_reach a B apos, fun ⟨_, _, r, e⟩ => e ▸ reach_of_run a B r⟩

theorem stateOf_inj (apos : ∀ i, 0 < a i) {L L' : List (Fin k)} {f f' : Nat}
    (h : stateOf a L f = stateOf a L' f') : f = f' ∧ ∀ i, (i ∈ L ↔ i ∈ L') := by
  refine ⟨by simpa using congrFun h (Fin.last k), fun i => ?_⟩
  have := congrFun h i.castSucc
  simp only [stateOf_cast] at this
  have := apos i
  by_cases m : i ∈ L <;> by_cases m' : i ∈ L' <;> simp_all <;> omega

/-- **The all-fired state is reachable iff the bundles can be binned.**  The
state with every sender fired and `r` chips at `v` is reachable exactly when
some order of all senders is a bin run ending at fill `r`. -/
theorem all_fired_reachable_iff (apos : ∀ i, 0 < a i) (r : Nat) :
    Reaches (Step a B) (stateOf a [] 0) (stateOf a (List.finRange k) r) ↔
      ∃ L, (∀ i, i ∈ L) ∧ Run a B L r := by
  rw [reach_iff a B apos]
  constructor
  · intro ⟨L, f, run, e⟩
    obtain ⟨hf, hm⟩ := stateOf_inj a apos e
    rw [hf]
    exact ⟨L, fun i => (hm i).mp (List.mem_finRange i), run⟩
  · intro ⟨L, all, run⟩
    refine ⟨L, r, run, ?_⟩
    funext u
    induction u using Fin.lastCases with
    | last => simp
    | cast i => simp [all i, List.mem_finRange i]

/-- **Getting stuck.**  A capacity-terminal state that is not ordinarily stable
is reachable exactly when some bin run leaves `v` short of full while every
unfired bundle is too big to fit. -/
theorem bad_terminal_reachable_iff (apos : ∀ i, 0 < a i) :
    (∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y) ↔
      ∃ L f, Run a B L f ∧ f < B ∧ (∃ i, i ∉ L) ∧ ∀ i, i ∉ L → B < f + a i := by
  constructor
  · intro ⟨y, hr, term, unstable⟩
    obtain ⟨L, f, run, rfl⟩ := run_of_reach a B apos hr
    have fle := run_le a B run
    have fB : f < B := by
      apply Classical.byContradiction
      intro h
      have e : f = B := by omega
      have lr := legal_receiver a B L
      rw [show stateOf a L B = stateOf a L f by rw [e]] at lr
      exact term _ lr
    refine ⟨L, f, run, fB, ?_, ?_⟩
    · apply Classical.byContradiction
      intro h
      apply unstable
      intro u
      induction u using Fin.lastCases with
      | last => simp [out]; exact fB
      | cast i =>
        have m : i ∈ L := Classical.byContradiction fun m => h ⟨i, m⟩
        simp [out, m]; exact apos i
    · intro i hi
      apply Classical.byContradiction
      intro h
      exact term _ (legal_sender a B L f i hi (by omega))
  · intro ⟨L, f, run, fB, ⟨i, hi⟩, stuck⟩
    refine ⟨stateOf a L f, reach_of_run a B run, ?_, ?_⟩
    · intro u ⟨unst, nb⟩
      induction u using Fin.lastCases with
      | last => simp [OrdinaryUnstable, out] at unst; omega
      | cast j =>
        have hj : j ∉ L := by
          intro m; simp [OrdinaryUnstable, out, m] at unst; have := apos j; omega
        exact nb ⟨Fin.last k, by simp [mult]; exact apos j, by simp [cap, mult]; exact stuck j hj⟩
    · intro stable
      have := stable i.castSucc
      simp [out, hi] at this

end Star

end CBMDFixedState
