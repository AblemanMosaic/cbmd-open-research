import OAI.Algorithms.SubexponentialSAT.SqrtLog.EntryClosedFormUnique

/-!
# Signed subword extraction for the entry closed-form bridge

This file evaluates the signed indicator over every sublist of a duplicate-free
coordinate list.  It is the combinatorial step needed to turn the unique native
delta contribution into its sign.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- The signed sublist sum selects one underlying subset, with the sign given by
its cardinality.  If the target subset is unavailable, the sum is zero. -/
theorem signed_sublists_indicator (as : List (Fin Q)) (has : as.Nodup)
    (T : Finset (Fin Q)) :
    (as.sublists'.map (fun bs =>
      (-1 : ℤ) ^ bs.length * if bs.toFinset = T then 1 else 0)).sum =
      if T ⊆ as.toFinset then (-1 : ℤ) ^ T.card else 0 := by
  classical
  by_cases hT : T ⊆ as.toFinset
  · let bs0 := as.filter (fun x => x ∈ T)
    have hsub : bs0.Sublist as := by
      exact List.filter_sublist
    have hmem : bs0 ∈ as.sublists' := List.mem_sublists'.2 hsub
    have hnodup0 : bs0.Nodup := hsub.nodup has
    have hfin : bs0.toFinset = T := by
      ext x
      simp only [bs0, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
      constructor
      · exact And.right
      · intro hx
        exact ⟨by simpa using hT hx, hx⟩
    rw [if_pos hT]
    rw [← List.sum_toFinset _ (List.nodup_sublists'.2 has)]
    rw [Finset.sum_eq_single bs0]
    · rw [if_pos hfin]
      simp only [mul_one]
      rw [← List.toFinset_card_of_nodup hnodup0, hfin]
    · intro bs hbs hne
      rw [if_neg]
      · simp
      · intro hbsfin
        have hbsmem : bs ∈ as.sublists' := by simpa using hbs
        have hbssub : bs.Sublist as := List.mem_sublists'.1 hbsmem
        have hnodupbs : bs.Nodup := hbssub.nodup has
        have hperm : bs.Perm bs0 :=
          List.perm_of_nodup_nodup_toFinset_eq hnodupbs hnodup0
            (hbsfin.trans hfin.symm)
        exact hne ((has.perm_iff_eq_of_sublist hbssub hsub).1 hperm)
    · intro hnot
      exact (hnot (by simpa using hmem)).elim
  · rw [if_neg hT]
    apply List.sum_eq_zero
    intro z hz
    rw [List.mem_map] at hz
    rcases hz with ⟨bs, hbs, rfl⟩
    rw [if_neg]
    · simp
    · intro hbsfin
      apply hT
      intro x hx
      have hxbs : x ∈ bs := by
        have : x ∈ bs.toFinset := by simpa [hbsfin] using hx
        simpa using this
      have hbssub : bs.Sublist as := List.mem_sublists'.1 hbs
      have hxas : x ∈ as := hbssub.subset hxbs
      simpa using hxas

/-- On an active selected set, the native integer difference is the signed
indicator that the selected set contains every non-pivot mismatch. -/
theorem integerDifference_active_subset (i : Fin Δ) (t : Fin Q)
    (u y : UniversalType r Q Δ) (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y) (S : Finset (Fin Q))
    (hpos : S ⊆ activePositions t) (hactive : S ⊆ activeSet i u) :
    integerDifference i S.toList (integerDelta y)
        (swapPositions i (activePositions t) u) =
      if (mismatches i u y).erase t ⊆ S then
        (-1 : ℤ) ^ ((mismatches i u y).erase t).card else 0 := by
  rw [integerDifference_expansion]
  have hmap :
      S.toList.sublists'.map (fun bs =>
        (-1 : ℤ) ^ bs.length *
          integerDelta y
            (applySwaps i bs (swapPositions i (activePositions t) u))) =
      S.toList.sublists'.map (fun bs =>
        (-1 : ℤ) ^ bs.length *
          if bs.toFinset = (mismatches i u y).erase t then 1 else 0) := by
    apply List.map_congr_left
    intro bs hbs
    have hbssub : bs.Sublist S.toList := List.mem_sublists'.1 hbs
    have hnodup : bs.Nodup := hbssub.nodup S.nodup_toList
    have hbsS : bs.toFinset ⊆ S := by
      intro x hx
      have hxbs : x ∈ bs := by simpa using hx
      have hxSList : x ∈ S.toList := hbssub.subset hxbs
      simpa using hxSList
    rw [integerDelta_applySwaps_active i t u y horbit ht bs hnodup
      (hbsS.trans hpos) (hbsS.trans hactive)]
  rw [hmap, signed_sublists_indicator S.toList S.nodup_toList]
  simp

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
