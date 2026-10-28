import OAI.Algorithms.SubexponentialSAT.LeanCompat

/-!
# Centered cancellation core

This file isolates the proved finite cancellation lemma from the still-open
source-transport obligations in `CenteredVanishing`.  It contains no admitted
axioms or proof escapes.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open scoped BigOperators

/-- The symmetric binomial factor in the central-line coefficient formula. -/
def centralBinomial (A k : ℕ) : ℤ :=
  ((A - 1 + k).choose k : ℤ)

/-- A summand in the central-line coefficient formula. -/
def centralTerm (A d k : ℕ) : ℤ :=
  (-1 : ℤ) ^ k * centralBinomial A k * centralBinomial A (d - k)

/-- The coefficient of degree `d` in the central-line product, without the
global factor `(-1)^A`. -/
def centralCoefficient (A d : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (d + 1), centralTerm A d k

private theorem centralTerm_reflect (A d k : ℕ) (hk : k ≤ d) (hd : Odd d) :
    centralTerm A d (d - k) = -centralTerm A d k := by
  have hsign : (-1 : ℤ) ^ (d - k) = -((-1 : ℤ) ^ k) := by
    by_cases heven : Even k
    · have hoddsub : Odd (d - k) := Nat.Odd.sub_even hk hd heven
      rw [hoddsub.neg_one_pow, heven.neg_one_pow]
    · have hoddk : Odd k := Nat.not_even_iff_odd.mp heven
      have hevensub : Even (d - k) := Nat.Odd.sub_odd hd hoddk
      rw [hevensub.neg_one_pow, hoddk.neg_one_pow]
      norm_num
  simp only [centralTerm, Nat.sub_sub_self hk, hsign]
  ring

/-- The central-line coefficient is zero in every odd degree. -/
theorem centralCoefficient_eq_zero_of_odd (A d : ℕ) (hd : Odd d) :
    centralCoefficient A d = 0 := by
  let S : ℤ := ∑ k ∈ Finset.range (d + 1), centralTerm A d k
  have hneg : S = -S := by
    calc
      S = ∑ k ∈ Finset.range (d + 1), centralTerm A d (d - k) := by
        simpa [S] using (Finset.sum_flip (fun k => centralTerm A d k)).symm
      _ = ∑ k ∈ Finset.range (d + 1), -centralTerm A d k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [centralTerm_reflect A d k (by simpa using hk) hd]
      _ = -S := by simp [S]
  unfold centralCoefficient
  change S = 0
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
