import OAI.Algorithms.SubexponentialSAT.SqrtLog.EntryClosedFormOrbit

/-!
# Superset count for the entry closed-form bridge

The guarded binomial coefficient is exactly the number of fixed-cardinality
active subsets containing every mismatch other than the pivot.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

variable {Q : ℕ}

/-- Count the `j`-element subsets of `D \ {t}` containing `M \ {t}`.  The
explicit guard is required because natural subtraction truncates below zero. -/
theorem card_powersetCard_filter_erase_subset (D M : Finset (Fin Q))
    (t : Fin Q) (j : ℕ) (hMD : M ⊆ D) (ht : t ∈ M) :
    (((D.erase t).powersetCard j).filter (M.erase t ⊆ ·)).card =
      if M.card - 1 ≤ j then
        (D.card - M.card).choose (j - (M.card - 1))
      else 0 := by
  have htD : t ∈ D := hMD ht
  have hsub : M.erase t ⊆ D.erase t := Finset.erase_subset_erase t hMD
  have hMpos : 1 ≤ M.card := Finset.one_le_card.mpr ⟨t, ht⟩
  have hcardMD : M.card ≤ D.card := Finset.card_le_card hMD
  have hDpos : 1 ≤ D.card := hMpos.trans hcardMD
  have hMreconstruct : M.card - 1 + 1 = M.card := Nat.sub_add_cancel hMpos
  have hDreconstruct : D.card - 1 + 1 = D.card := Nat.sub_add_cancel hDpos
  have hdiff : (D.card - 1) - (M.card - 1) = D.card - M.card := by omega
  have hMcard : (M.erase t).card = M.card - 1 := Finset.card_erase_of_mem ht
  have hDcard : (D.erase t).card = D.card - 1 := Finset.card_erase_of_mem htD
  by_cases hle : M.card - 1 ≤ j
  · rw [if_pos hle]
    have hsn : (M.erase t).card ≤ j := by
      rw [hMcard]
      exact hle
    rw [Finset.card_filter_powersetCard_subset (M.erase t) (D.erase t) j hsub hsn]
    rw [hMcard, hDcard]
    rw [hdiff]
  · rw [if_neg hle, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    have hfilter := Finset.mem_filter.mp hS
    have hcard := (Finset.mem_powersetCard.mp hfilter.1).2
    have hcardle := Finset.card_le_card hfilter.2
    rw [hMcard, hcard] at hcardle
    exact hle hcardle

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
