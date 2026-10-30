import CBMDFixedState.Bins

/-!
# Getting stuck on the star leaves a residue witness

A bin run that gets stuck has fired a set `L` of senders and left the receiver
holding `f < B` chips.  Because the closed blocks each hold exactly `B`, the
fill is the residue of the fired total: `f = (lsum L) % B` (`fill_eq_mod`).
So a stuck run hands over a **residue witness**: a set `F` of senders, missing
at least one, such that every sender outside `F` is too big to fit on top of
`(lsum F) % B` (`stuck_imp_witness`).

The witness condition mentions only a residue modulo `B`, not an order or a
packing.  Its absence is therefore a certificate of safety
(`safe_of_no_witness`): if no set of senders is a residue witness, no
capacity-blocked run from the start state ends in a bad terminal state.

The converse — every residue witness can be realised by an actual run — is
**not** proved here; it is a conjecture recorded with its evidence in the
dossier.
-/

namespace CBMDFixedState

namespace Star

variable {k : Nat} (a : Fin k → Nat) (B : Nat)

/-- A **residue witness**: `F` misses some sender, and every sender outside `F`
overflows the receiver when added to the residue of `F`'s total. -/
def ResidueWitness (F : List (Fin k)) : Prop :=
  F.Nodup ∧ (∃ i, i ∉ F) ∧ ∀ i, i ∉ F → B < lsum a F % B + a i

theorem lsum_blocks : ∀ (bs : List (List (Fin k))),
    (∀ b ∈ bs, lsum a b = B) → lsum a bs.flatten = bs.length * B
  | [], _ => by simp
  | b :: bs, h => by
    rw [List.flatten_cons, lsum_append, h b List.mem_cons_self,
      lsum_blocks bs (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))]
    simp [Nat.succ_mul, Nat.add_comm]

/-- **The fill of a run is the residue of the fired total** (when short of full). -/
theorem fill_eq_mod {L : List (Fin k)} {f : Nat} (run : Run a B L f) (fB : f < B) :
    lsum a L % B = f := by
  obtain ⟨_, _, bs, o, e, sums, so⟩ := (run_iff_blocks a B L f).mp run
  subst e
  rw [lsum_append, lsum_blocks a B bs sums, so, Nat.mul_comm, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt fB

/-- **A stuck run yields a residue witness.** -/
theorem stuck_imp_witness :
    (∃ L f, Run a B L f ∧ f < B ∧ (∃ i, i ∉ L) ∧ ∀ i, i ∉ L → B < f + a i) →
      ∃ F, ResidueWitness a B F := by
  intro ⟨L, f, run, fB, ex, stuck⟩
  refine ⟨L, run_nodup a B run, ex, ?_⟩
  intro i hi
  rw [fill_eq_mod a B run fB]
  exact stuck i hi

/-- **No residue witness, no bad ending.**  If no set of senders is a residue
witness, then no capacity-terminal state reachable from the start is
ordinarily unstable. -/
theorem safe_of_no_witness (apos : ∀ i, 0 < a i) (h : ∀ F, ¬ ResidueWitness a B F) :
    ¬ ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  intro hy
  obtain ⟨F, hF⟩ := stuck_imp_witness a B ((bad_terminal_reachable_iff a B apos).mp hy)
  exact h F hF

end Star

end CBMDFixedState
