import OAI.Algorithms.SubexponentialSAT.SqrtLog.MasterNumeratorLinear

/-!
# Shared recurrence table for the master numerator

The reversed table is built with exactly one arithmetic recurrence step per
new coefficient.  List construction and reversal are not yet assigned a cost;
the theorem in this module is only about exact values and explicit sharing.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator

open Finset
open SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

/-- `[C(N,d), C(N,d-1), ..., C(N,0)]`, built by extending the prior table once. -/
def generalizedChooseRev (N : ℤ) : ℕ → List ℤ
  | 0 => [1]
  | d + 1 =>
      let previous := generalizedChooseRev N d
      let next := previous.headD 0 * (N - (d : ℤ)) / ((d + 1 : ℕ) : ℤ)
      next :: previous

theorem generalizedChooseRev_eq (N : ℤ) : ∀ d : ℕ,
    generalizedChooseRev N d =
      (List.range (d + 1)).reverse.map (fun k => Ring.choose N k) := by
  intro d
  induction d with
  | zero => simp [generalizedChooseRev]
  | succ d ih =>
      have hstep :
          Ring.choose N d * (N - (d : ℤ)) / ((d + 1 : ℕ) : ℤ) =
            Ring.choose N (d + 1) := by
        apply Int.ediv_eq_of_eq_mul_left
        · omega
        · exact ringChoose_mul_step N d
      have hstep' :
          Ring.choose N d * (N - (d : ℤ)) / ((d : ℤ) + 1) =
            Ring.choose N (d + 1) := by
        simpa using hstep
      rw [generalizedChooseRev, ih]
      simp [List.range_succ, hstep']

/-- The same shared coefficient table in ascending index order. -/
def generalizedChooseTable (N : ℤ) (d : ℕ) : List ℤ :=
  (generalizedChooseRev N d).reverse

theorem generalizedChooseTable_eq (N : ℤ) (d : ℕ) :
    generalizedChooseTable N d =
      (List.range (d + 1)).map (fun k => Ring.choose N k) := by
  simp [generalizedChooseTable, generalizedChooseRev_eq, List.map_reverse]

private theorem zipWith_map_same
    {X Y Z W : Type} (xs : List X) (f : X → Y) (g : X → Z)
    (op : Y → Z → W) :
    List.zipWith op (xs.map f) (xs.map g) =
      xs.map (fun x => op (f x) (g x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

/-- `[g₀,…,g_d]`, where `g_k` is the negative-binomial factor, with the
underlying generalized coefficients generated once.  Sign normalization is
explicit and is not included in any arithmetic-cost claim yet. -/
def negativeBinomialTable (A d : ℕ) : List ℤ :=
  List.zipWith (fun sign coefficient => sign * coefficient)
    ((List.range (d + 1)).map (fun k => (-1 : ℤ) ^ k))
    (generalizedChooseTable (-(A : ℤ)) d)

theorem negativeBinomialTable_eq (A d : ℕ) :
    negativeBinomialTable A d =
      (List.range (d + 1)).map (negativeBinomialCoeff A) := by
  rw [negativeBinomialTable, generalizedChooseTable_eq,
    zipWith_map_same]
  apply List.map_congr_left
  intro k hk
  rw [← generalizedChooseLinear_eq_ringChoose]
  exact negativeBinomialLinear_eq A k

theorem generalizedChooseTable_getD (N : ℤ) (d k : ℕ) (hk : k ≤ d) :
    (generalizedChooseTable N d).getD k 0 = Ring.choose N k := by
  rw [generalizedChooseTable_eq]
  have hk' : k < d + 1 := by omega
  simp [List.getD, hk']

theorem negativeBinomialTable_getD (A d k : ℕ) (hk : k ≤ d) :
    (negativeBinomialTable A d).getD k 0 = negativeBinomialCoeff A k := by
  rw [negativeBinomialTable_eq]
  have hk' : k < d + 1 := by omega
  simp [List.getD, hk']

/-- Master amplitude whose two complete coefficient tables are let-bound once
and then indexed by the finite convolution.  This establishes value sharing;
list traversal, storage, and sign normalization remain uncharged. -/
def masterAlphaShared (A R δ f : ℕ) : ℤ :=
  let d := R - 1 - f
  let chooseTable := generalizedChooseTable
    ((A : ℤ) + (R : ℤ) - (δ : ℤ)) d
  let negativeTable := negativeBinomialTable A d
  (-1 : ℤ) ^ A *
    ∑ k ∈ range (d + 1),
      chooseTable.getD k 0 * negativeTable.getD (d - k) 0

def masterNumeratorShared (A R δ f : ℕ) : ℤ :=
  2 ^ (R - 1) * masterAlphaShared A R δ f

theorem masterAlphaShared_eq_masterAlpha (A R δ f : ℕ) :
    masterAlphaShared A R δ f = masterAlpha A R δ f := by
  simp only [masterAlphaShared, masterAlpha]
  apply congrArg ((-1 : ℤ) ^ A * ·)
  apply Finset.sum_congr rfl
  intro k hk
  have hklt : k < R - 1 - f + 1 := Finset.mem_range.mp hk
  have hkle : k ≤ R - 1 - f := by omega
  rw [generalizedChooseTable_getD _ _ _ hkle,
    negativeBinomialTable_getD _ _ _ (Nat.sub_le _ _),
    generalizedChoose_eq_ringChoose]

theorem masterNumeratorShared_eq_masterNumerator (A R δ f : ℕ) :
    masterNumeratorShared A R δ f = masterNumerator A R δ f := by
  rw [masterNumeratorShared, masterNumerator,
    masterAlphaShared_eq_masterAlpha]

/-- Native source entry bound to the shared-table executable value route. -/
theorem entry_eq_masterNumeratorShared
    (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ)
    (horbit : InOrbit i u y)
    (ht : t ∈ mismatches i u y)
    (hMleR : (mismatches i u y).card ≤ R) :
    entry i t A R u y =
      masterNumeratorShared A R (activeSet i u).card
        ((mismatches i u y).card - 1) := by
  rw [masterNumeratorShared_eq_masterNumerator]
  exact entry_eq_masterNumerator i t A R u y horbit ht hMleR

end OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator
