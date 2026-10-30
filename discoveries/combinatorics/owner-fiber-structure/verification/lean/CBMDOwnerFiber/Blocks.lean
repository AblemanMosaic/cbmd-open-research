import CBMDOwnerFiber.Core

/-!
# Several blocks

The packed reference places incidences in **blocks**: an incidence's block is
its rank among the earlier incidences carrying the same label, in list order
(first occurrence is block 0, the next block 1, and so on).  Contributions are
only counted between incidences in the same block.  This module compiles the
unique-contributor statement with blocks, and proves the packing invariant it
needs from that rank definition itself.
-/

namespace CBMDOwnerFiber

variable {Q r : Nat}

/-- Rank of position `i` among equal labels before it. -/
def rankAt {α : Type} [DecidableEq α] (l : List α) (i : Nat) (h : i < l.length) : Nat :=
  (l.take i).count (l[i]'h)

/-- **The packing invariant.**  Two positions with the same label have different
ranks; so within one block each label occurs at most once. -/
theorem rank_injective {α : Type} [DecidableEq α] (l : List α) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (same : l[i] = l[j])
    (rank : rankAt l i hi = rankAt l j hj) : i = j := by
  apply Classical.byContradiction
  intro ne
  -- order the two positions
  have key : ∀ a b (ha : a < l.length) (hb : b < l.length), a < b → l[a] = l[b] →
      rankAt l a ha < rankAt l b hb := by
    intro a b ha hb hab e
    unfold rankAt
    have split : l.take b = l.take a ++ (l.take b).drop a := by
      have h1 := (List.take_append_drop a (l.take b)).symm
      rw [List.take_take] at h1
      first
        | (rw [Nat.min_eq_left (Nat.le_of_lt hab)] at h1; exact h1)
        | (rw [Nat.min_eq_right (Nat.le_of_lt hab)] at h1; exact h1)
    rw [split, List.count_append, ← e]
    have mem : l[a] ∈ (l.take b).drop a := by
      have hlen : 0 < ((l.take b).drop a).length := by
        simp only [List.length_drop, List.length_take]; omega
      have : ((l.take b).drop a)[0]'hlen = l[a] := by
        simp only [List.getElem_drop, List.getElem_take, Nat.add_zero]
      rw [← this]; exact List.getElem_mem hlen
    have := List.count_pos_iff.mpr mem
    omega
  rcases Nat.lt_or_gt_of_ne ne with h | h
  · have := key i j hi hj h same; omega
  · have := key j i hj hi h same.symm; omega

/-- **Unique contributor, with blocks.**  Labels decode injectively to types; a
target in block `b` receives contributions only from incidences in block `b`.
Then for a fixed owner at most one incidence contributes. -/
theorem unique_contributor_blocks {α Owner : Type} [DecidableEq α]
    (l : List α) (decode : α → Typ Q r) (decode_inj : ∀ a c, decode a = decode c → a = c)
    (owner : Fin l.length → Owner) (headOf : Owner → (Fin Q → Fin r))
    (Support : Typ Q r → Typ Q r → Prop)
    (support_in_orbit : ∀ u y, Support u y → InOrbit u y)
    (coherent : ∀ i : Fin l.length, headOf (owner i) = (decode l[i]).head)
    (u : Typ Q r) (b : Nat) (v : Owner) {i j : Fin l.length}
    (bi : rankAt l i i.isLt = b) (bj : rankAt l j j.isLt = b)
    (oi : owner i = v) (oj : owner j = v)
    (si : Support u (decode l[i])) (sj : Support u (decode l[j])) : i = j := by
  have types : decode l[i] = decode l[j] := by
    refine orbit_head_injective (support_in_orbit _ _ si) (support_in_orbit _ _ sj) (fun t => ?_)
    rw [← coherent i, ← coherent j, oi, oj]
  have labels : l[i] = l[j] := decode_inj _ _ types
  exact Fin.ext (rank_injective l i.isLt j.isLt labels (bi.trans bj.symm))

/-- **The class-count bound, with blocks.**  Two targets in the same block and
the same orbit class share their contributor for a fixed owner, so per owner
the contributors are at most the distinct (block, orbit-class) pairs. -/
theorem contributor_class_injective_blocks {α Owner : Type} [DecidableEq α]
    (l : List α) (decode : α → Typ Q r) (decode_inj : ∀ a c, decode a = decode c → a = c)
    (owner : Fin l.length → Owner) (headOf : Owner → (Fin Q → Fin r))
    (Support : Typ Q r → Typ Q r → Prop)
    (support_in_orbit : ∀ u y, Support u y → InOrbit u y)
    (coherent : ∀ i : Fin l.length, headOf (owner i) = (decode l[i]).head)
    {u u' : Typ Q r} (same_class : InOrbit u u') (b : Nat) (v : Owner) {i j : Fin l.length}
    (bi : rankAt l i i.isLt = b) (bj : rankAt l j j.isLt = b)
    (oi : owner i = v) (oj : owner j = v)
    (si : Support u (decode l[i])) (sj : Support u' (decode l[j])) : i = j := by
  have oy := support_in_orbit _ _ si
  have oz := inOrbit_trans same_class (support_in_orbit _ _ sj)
  have types : decode l[i] = decode l[j] := by
    refine orbit_head_injective oy oz (fun t => ?_)
    rw [← coherent i, ← coherent j, oi, oj]
  exact Fin.ext (rank_injective l i.isLt j.isLt (decode_inj _ _ types) (bi.trans bj.symm))

end CBMDOwnerFiber
