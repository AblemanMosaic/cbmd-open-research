/-!
# The owner fiber has at most one contributor

`CBMD-COMB-OWNER-FIBER-001` checks by census that a fixed covered target and
requested owner admit at most one nonzero contributing source row, and that the
contributor is the orbit element carrying the owner's head word.  This compiles
both, from the two properties the census actually relies on.

A universal type is a pair of words of length `Q` over an alphabet of size `r`:
a **head** and a **slot**.  Two types lie in the same **orbit** when, at every
coordinate, the unordered pair `{head, slot}` agrees — each coordinate is
either left alone or swapped.

Two inputs, and nothing else about the model is needed:

* `support_in_orbit` — a source row can only be nonzero at a type in the
  target's orbit.  In the reference model this is immediate: the row is the
  indicator at `y = u` minus a term that vanishes off the orbit.
* `coherent` — full-head coherence: a column's head word is its owner's head
  word.

From those, orbit elements with equal heads are equal (`orbit_head_injective`),
so a fixed owner has at most one contributor (`unique_contributor`), and that
contributor is the explicit `candidate` (`contributor_eq_candidate`).

The orbit-head injectivity that the written claim lists as a premise is
**derived** here rather than assumed.  The one place it could fail is a
coordinate where the target's head and slot differ and the requested head
matches neither; `candidate` is partial for exactly that reason.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDOwnerFiber

variable {Q r : Nat}

/-- A universal type: a head word and a slot word. -/
structure Typ (Q r : Nat) where
  head : Fin Q → Fin r
  slot : Fin Q → Fin r

theorem Typ.ext {y z : Typ Q r} (h : ∀ t, y.head t = z.head t)
    (s : ∀ t, y.slot t = z.slot t) : y = z := by
  cases y; cases z
  simp only [Typ.mk.injEq]
  exact ⟨funext h, funext s⟩

/-- Same orbit: every coordinate is either untouched or swapped. -/
def InOrbit (u y : Typ Q r) : Prop :=
  ∀ t, (y.head t = u.head t ∧ y.slot t = u.slot t) ∨
       (y.head t = u.slot t ∧ y.slot t = u.head t)

theorem inOrbit_refl (u : Typ Q r) : InOrbit u u :=
  fun _ => Or.inl ⟨rfl, rfl⟩

/-- **Orbit elements are determined by their head.**  Derived, not assumed. -/
theorem orbit_head_injective {u y z : Typ Q r}
    (oy : InOrbit u y) (oz : InOrbit u z)
    (h : ∀ t, y.head t = z.head t) : y = z := by
  refine Typ.ext h (fun t => ?_)
  rcases oy t with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩ <;> rcases oz t with ⟨hz1, hz2⟩ | ⟨hz1, hz2⟩
  · rw [hy2, hz2]
  · -- y untouched, z swapped: the heads force the target's own head and slot to agree
    have : u.head t = u.slot t := by rw [← hy1, h t, hz1]
    rw [hy2, hz2, this]
  · have : u.slot t = u.head t := by rw [← hy1, h t, hz1]
    rw [hy2, hz2, this]
  · rw [hy2, hz2]

/-- **At most one contributor per owner.**  `Support u y` is any predicate whose
witnesses lie in the orbit; `own` assigns an owner to each type and `headOf`
gives each owner its head word. -/
theorem unique_contributor {Owner : Type}
    (Support : Typ Q r → Typ Q r → Prop)
    (own : Typ Q r → Owner) (headOf : Owner → (Fin Q → Fin r))
    (support_in_orbit : ∀ u y, Support u y → InOrbit u y)
    (coherent : ∀ y, headOf (own y) = y.head)
    (u : Typ Q r) (v : Owner) {y z : Typ Q r}
    (hy : own y = v) (hz : own z = v)
    (sy : Support u y) (sz : Support u z) : y = z := by
  refine orbit_head_injective (support_in_orbit u y sy) (support_in_orbit u z sz)
    (fun t => ?_)
  have ey : headOf v t = y.head t := by rw [← hy, coherent y]
  have ez : headOf v t = z.head t := by rw [← hz, coherent z]
  rw [← ey, ez]

/-! ## Naming the contributor -/

/-- The orbit element carrying a requested head word, where one exists. -/
def candidate [DecidableEq (Fin r)] (u : Typ Q r) (h : Fin Q → Fin r) : Typ Q r where
  head := h
  slot := fun t => if h t = u.head t then u.slot t else u.head t

theorem candidate_head [DecidableEq (Fin r)] (u : Typ Q r) (h : Fin Q → Fin r) :
    (candidate u h).head = h := rfl

/-- The candidate is in the orbit exactly when the requested head is reachable:
at every coordinate it must be the target's head or its slot. -/
theorem candidate_inOrbit [DecidableEq (Fin r)] (u : Typ Q r) (h : Fin Q → Fin r)
    (ok : ∀ t, h t = u.head t ∨ h t = u.slot t) : InOrbit u (candidate u h) := by
  intro t
  by_cases hc : h t = u.head t
  · exact Or.inl ⟨hc, by simp [candidate, hc]⟩
  · have hs : h t = u.slot t := (ok t).resolve_left hc
    exact Or.inr ⟨hs, by simp [candidate, hc]⟩

/-- **The contributor is the candidate.**  Any orbit element whose head is the
owner's head word is the explicit `candidate`, so the census's lookup is not a
coincidence of the sampled layouts. -/
theorem contributor_eq_candidate [DecidableEq (Fin r)] {u y : Typ Q r}
    {h : Fin Q → Fin r} (oy : InOrbit u y) (hh : ∀ t, y.head t = h t)
    (ok : ∀ t, h t = u.head t ∨ h t = u.slot t) : y = candidate u h :=
  orbit_head_injective oy (candidate_inOrbit u h ok) hh

/-- Every orbit element's head is one of the target's two letters at each
coordinate.  True at every coordinate, active or not — stated separately so the
next lemma, which really does need activity, is not confused with it. -/
theorem orbit_head_mem {u y : Typ Q r} (oy : InOrbit u y) (t : Fin Q) :
    y.head t = u.head t ∨ y.head t = u.slot t := by
  rcases oy t with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Or.inl h1
  · exact Or.inr h1

/-- **Why coherence is needed on active coordinates.**  Where the target's head
and slot differ, the head of an orbit element settles whether that coordinate
was swapped; where they agree, it settles nothing and nothing needs settling.
This is the content behind the written claim's activity condition, and the
reason a head that is wrong at an active coordinate names no orbit element. -/
theorem active_head_determines_swap {u y : Typ Q r} (oy : InOrbit u y) {t : Fin Q}
    (active : u.head t ≠ u.slot t) :
    (y.head t = u.head t → y.slot t = u.slot t) ∧
      (y.head t = u.slot t → y.slot t = u.head t) := by
  rcases oy t with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun hc => absurd (h1 ▸ hc) active⟩
  · exact ⟨fun hc => absurd (h1 ▸ hc).symm active, fun _ => h2⟩

end CBMDOwnerFiber
