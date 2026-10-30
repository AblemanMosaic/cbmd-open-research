import CBMDFixedState.Star

/-!
# Bin runs are partitions into exact bins

A bin run is a list of fired senders; the fill rises by each bundle and resets
when it reaches `B`.  This module proves that bin runs are exactly the lists
that split into consecutive **blocks of total exactly `B`**, followed by an open
block of total at most `B` (`run_iff_blocks`).  With every sender fired and the
open block empty, that is the question "can the bundles be partitioned into
groups each of total `B`?" — bin packing with exact fill, of which 3-PARTITION
is the special case (`normal_form_reachable_iff_partition`).
-/

namespace CBMDFixedState

namespace Star

variable {k : Nat} (a : Fin k → Nat) (B : Nat)

def lsum (l : List (Fin k)) : Nat := (l.map a).sum

@[simp] theorem lsum_nil : lsum a [] = 0 := rfl
@[simp] theorem lsum_cons (i : Fin k) (l : List (Fin k)) : lsum a (i :: l) = a i + lsum a l := by
  simp [lsum]
theorem lsum_append (l l' : List (Fin k)) : lsum a (l ++ l') = lsum a l + lsum a l' := by
  simp [lsum, List.sum_append]

theorem run_nodup {L : List (Fin k)} {f : Nat} (r : Run a B L f) : L.Nodup := by
  induction r with
  | nil => exact List.nodup_nil
  | add i _ hi _ ih =>
    rw [List.nodup_append]
    exact ⟨ih, (by simp : [i].Nodup), fun x hx y hy => by
      simp at hy; subst hy; exact fun e => hi (e ▸ hx)⟩
  | reset _ ih => exact ih

/-- Appending a list of fresh senders that fits. -/
theorem run_extend : ∀ (o : List (Fin k)) {L : List (Fin k)} {f : Nat},
    Run a B L f → (L ++ o).Nodup → f + lsum a o ≤ B → Run a B (L ++ o) (f + lsum a o)
  | [], L, f, r, _, _ => by simpa using r
  | i :: o, L, f, r, nd, fits => by
    have hi : i ∉ L := by
      intro m
      rw [List.nodup_append] at nd
      exact nd.2.2 i m i (List.mem_cons_self) rfl
    have r1 : Run a B (L ++ [i]) (f + a i) := Run.add i r hi (by simp at fits; omega)
    have := run_extend o r1 (by simpa using nd) (by simp at fits; omega)
    simpa [Nat.add_assoc] using this

theorem run_blocks : ∀ (bs : List (List (Fin k))) {L : List (Fin k)},
    Run a B L 0 → (L ++ bs.flatten).Nodup → (∀ b ∈ bs, lsum a b = B) → Run a B (L ++ bs.flatten) 0
  | [], L, r, _, _ => by simpa using r
  | b :: bs, L, r, nd, sums => by
    have hb := sums b (List.mem_cons_self)
    have nd1 : (L ++ b).Nodup := by
      simp only [List.flatten_cons] at nd
      exact (List.nodup_append.mp (by simpa [List.append_assoc] using nd)).1
    have r1 : Run a B (L ++ b) B := by
      have := run_extend a B b r nd1 (by omega)
      simpa [hb] using this
    have := run_blocks bs (Run.reset r1) (by simpa [List.append_assoc] using nd)
      (fun b' hb' => sums b' (List.mem_cons_of_mem _ hb'))
    simpa [List.append_assoc] using this

/-- **Bin runs are block decompositions.** -/
theorem run_iff_blocks (L : List (Fin k)) (r : Nat) :
    Run a B L r ↔ L.Nodup ∧ r ≤ B ∧ ∃ (bs : List (List (Fin k))) (o : List (Fin k)),
      L = bs.flatten ++ o ∧ (∀ b ∈ bs, lsum a b = B) ∧ lsum a o = r := by
  constructor
  · intro run
    refine ⟨run_nodup a B run, run_le a B run, ?_⟩
    induction run with
    | nil => exact ⟨[], [], rfl, by simp, rfl⟩
    | add i _ _ _ ih =>
      obtain ⟨bs, o, e, sums, so⟩ := ih
      exact ⟨bs, o ++ [i], by rw [e, List.append_assoc], sums, by rw [lsum_append, so]; simp [lsum]⟩
    | reset _ ih =>
      obtain ⟨bs, o, e, sums, so⟩ := ih
      refine ⟨bs ++ [o], [], by simp [e], ?_, rfl⟩
      intro b hb
      simp at hb
      rcases hb with hb | hb
      · exact sums b hb
      · subst hb; exact so
  · intro ⟨nd, rle, bs, o, e, sums, so⟩
    subst e
    have r0 : Run a B ([] ++ bs.flatten) 0 :=
      run_blocks a B bs Run.nil (by simpa using (List.nodup_append.mp nd).1) sums
    have := run_extend a B o (by simpa using r0) nd (by omega)
    simpa [so] using this

/-- **The normal form of a multiple-of-`B` instance is reachable iff the senders
partition into groups of total exactly `B`.**  Bundles are positive; the
all-fired state with `v` empty is reachable exactly when some list of disjoint
blocks covering every sender has every block of total `B`. -/
theorem normal_form_reachable_iff_partition (apos : ∀ i, 0 < a i) :
    Reaches (Step a B) (stateOf a [] 0) (stateOf a (List.finRange k) 0) ↔
      ∃ bs : List (List (Fin k)), bs.flatten.Nodup ∧ (∀ i, i ∈ bs.flatten) ∧
        ∀ b ∈ bs, lsum a b = B := by
  rw [all_fired_reachable_iff a B apos]
  constructor
  · intro ⟨L, all, run⟩
    obtain ⟨nd, _, bs, o, e, sums, so⟩ := (run_iff_blocks a B L 0).mp run
    -- the open block has total 0, so it is empty
    have oe : o = [] := by
      cases o with
      | nil => rfl
      | cons i o => simp at so; have := apos i; omega
    subst oe
    simp at e
    subst e
    exact ⟨bs, nd, all, sums⟩
  · intro ⟨bs, nd, all, sums⟩
    exact ⟨bs.flatten, all, (run_iff_blocks a B _ 0).mpr
      ⟨nd, Nat.zero_le _, bs, [], by simp, sums, rfl⟩⟩

end Star

end CBMDFixedState
