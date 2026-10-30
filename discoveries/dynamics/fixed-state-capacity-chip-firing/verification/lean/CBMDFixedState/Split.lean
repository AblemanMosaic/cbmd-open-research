import CBMDFixedState.ResidueDecide

/-!
# Witnesses that split into a small part and pairwise-overflowing rest

A residue witness `U` **splits** as `T ⊔ W` when `T` totals at most `B`, every
member of `W` overflows on top of `T`, and any two members of `W` overflow
together.  Every such witness is realised by a stuck run (`realise_split`).

This covers every witness with at most three unfired senders, every witness in
which no two unfired senders fit together, and every witness that becomes
small after dropping one sender.  The proof follows one explicit run: close
`T` with fired-part bundles, then a maximal fired-part packing topped up by one
`W` bundle, then pack what is left; comparing totals contradicts the residue.
-/

namespace CBMDFixedState

namespace Star

variable {k : Nat} (a : Fin k → Nat) (B : Nat)

/-- **A witness that splits as `T ⊔ W` is realised.** -/
theorem realise_split (apos : ∀ i, 0 < a i) (Bpos : 0 < B) :
    ∀ (n : Nat) (L : List (Fin k)), ps a (avail L) ≤ n → Run a B L 0 →
      ∀ T W : Fin k → Bool,
        (∀ i, T i = true → avail L i = true) → (∀ i, W i = true → avail L i = true) →
        (∀ i, T i = true → W i = false) → (∃ u, T u = true ∨ W u = true) →
        ps a T ≤ B → (∀ w, W w = true → B < ps a T + a w) →
        (∀ w w', W w = true → W w' = true → w ≠ w' → B < a w + a w') →
        (∀ u, (T u || W u) = true → B < ps a (Fp L (fun i => T i || W i)) % B + a u) →
        Stuck a B := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro L hn run T W hTL hWL hTW hne hTB hTw hWW wit
  let U : Fin k → Bool := fun i => T i || W i
  have wit : ∀ u, U u = true → B < ps a (Fp L U) % B + a u := wit
  have hUL : ∀ u, U u = true → avail L u = true := by
    intro u hu
    simp only [U, Bool.or_eq_true] at hu
    rcases hu with h | h
    · exact hTL u h
    · exact hWL u h
  have hneU : ∃ u, U u = true := by
    obtain ⟨u, h⟩ := hne; exact ⟨u, by simp [U, h]⟩
  -- no W: the witness is small
  by_cases hWf : ∀ i, W i = false
  · have hUT : ps a U = ps a T := ps_congr a (fun i => by simp [U, hWf i])
    exact realise_small a B apos Bpos _ L (Nat.le_refl _) run U hneU hUL (by omega) wit
  obtain ⟨w0, hw0⟩ : ∃ w, W w = true := by
    apply Classical.byContradiction
    intro hno
    exact hWf (fun i => by
      cases h : W i
      · rfl
      · exact absurd ⟨i, h⟩ hno)
  apply Classical.byContradiction
  intro nost
  -- (b) no exact block inside the fired part
  have noexact : ∀ E : Fin k → Bool, (∀ i, E i = true → Fp L U i = true) → ps a E ≠ B := by
    intro E hEF hEB
    have run' := run_exact a B run E (fun i h => Fp_avail (hEF i h)) hEB
    have cl := ps_avail_close a L E (fun i h => Fp_avail (hEF i h))
    obtain ⟨hav, wit'⟩ := witness_after_block a B U E hEF hEB wit
    apply nost
    refine ih _ (by omega) _ (Nat.le_refl _) run' T W
      (fun i h => hav i (by simp [U, h]) (hTL i h)) (fun i h => hav i (by simp [U, h]) (hWL i h))
      hTW hne hTB hTw hWW wit'
  have Fbig := fbig a B run U hneU hUL wit nost
  have split := ps_avail_split a L U hUL
  have big : B ≤ ps a (avail L) := by omega
  have hUF : ∀ i, Fp L U i = true ↔ (avail L i = true ∧ T i = false ∧ W i = false) := by
    intro i; simp only [Fp, U, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff]
  -- Stage 1: extend T maximally; the block C1 is exact and contains no W bundle
  obtain ⟨C1, hTC1, hC1L, hC1B, hC1max⟩ :=
    exists_maximal a B apos (avail L) _ T (Nat.le_refl _) hTL hTB
  have hC1eq := maxExact a B run nost big C1 hC1L hC1max hC1B
  have c1split := ps_split a C1 T
  have c1t : ps a (fun i => C1 i && T i) = ps a T := by
    apply ps_congr; intro i
    cases ht : T i
    · simp
    · simp [hTC1 i ht]
  have hC1W : ∀ i, W i = true → C1 i = false := by
    intro i hwi
    cases hc : C1 i
    · rfl
    · have hti : T i = false := by
        cases ht : T i
        · rfl
        · have := hTW i ht; rw [hwi] at this; cases this
      have := ps_ge a (fun j => C1 j && !T j) i (by simp [hc, hti])
      have := hTw i hwi
      omega
  have run1 := run_exact a B run C1 hC1L hC1eq
  have cl1 := ps_avail_close a L C1 hC1L
  have av1 : ∀ i, avail (L ++ lst C1) i = (avail L i && !C1 i) := avail_append L C1
  -- the rest of the fired part
  let F2 : Fin k → Bool := fun i => avail (L ++ lst C1) i && !U i
  have hF2F : ∀ i, F2 i = true → Fp L U i = true := by
    intro i h
    simp only [F2, av1, Bool.and_eq_true, Bool.not_eq_true'] at h
    simp [Fp, h.1.1, h.2]
  have fsplit := ps_split a (Fp L U) C1
  have f1 : ps a (fun i => Fp L U i && C1 i) = ps a (fun i => C1 i && !T i) := by
    apply ps_congr; intro i
    cases hc : C1 i
    · simp
    · have hav := hC1L i hc
      cases ht : T i
      · cases hw : W i
        · simp [Fp, U, hav, ht, hw]
        · rw [hC1W i hw] at hc; cases hc
      · simp [Fp, U, ht]
  have f2 : ps a (fun i => Fp L U i && !C1 i) = ps a F2 := by
    apply ps_congr; intro i
    simp only [F2, Fp, av1]
    cases avail L i <;> cases C1 i <;> cases U i <;> simp
  -- Stage 2: a maximal subset P of F2; some W bundle fits on top
  obtain ⟨P, -, hPF2, hPB, hPmax⟩ :=
    exists_maximal a B apos F2 _ (fun _ => false) (Nat.le_refl _) (fun i h => by simp at h)
      (by rw [ps_zero a _ (fun _ => rfl)]; exact Nat.zero_le _)
  have hPF : ∀ i, P i = true → Fp L U i = true := fun i h => hF2F i (hPF2 i h)
  have hPlt : ps a P < B := by have := noexact P hPF; omega
  have hPL1 : ∀ i, P i = true → avail (L ++ lst C1) i = true := by
    intro i h
    have := hPF2 i h
    simp only [F2, Bool.and_eq_true] at this
    exact this.1
  have hW1 : ∀ i, W i = true → avail (L ++ lst C1) i = true := by
    intro i h; rw [av1]; simp [hWL i h, hC1W i h]
  have hPW : ∀ i, W i = true → P i = false := by
    intro i h
    cases hp : P i
    · rfl
    · have := Fp_notU (hPF i hp); simp [U, h] at this
  have rest1 : ∀ i, avail (L ++ lst C1) i = true → W i = true ∨ F2 i = true := by
    intro i h
    cases hw : W i
    · right
      have hti : T i = false := by
        cases ht : T i
        · rfl
        · rw [av1] at h; simp [hTC1 i ht] at h
      simp [F2, U, h, hti, hw]
    · left; rfl
  obtain ⟨w1, hw1, hfit⟩ : ∃ w, W w = true ∧ ps a P + a w ≤ B := by
    apply Classical.byContradiction
    intro hno
    apply nost
    apply stuck_of_maximal a B run1 P hPL1 hPlt
    · intro i hav hp
      rcases rest1 i hav with h | h
      · apply Classical.byContradiction
        intro hle
        exact hno ⟨i, h, by omega⟩
      · exact hPmax i h hp
    · exact ⟨w0, hW1 w0 hw0, hPW w0 hw0⟩
  let C2 : Fin k → Bool := fun i => P i || decide (i = w1)
  have psC2 : ps a C2 = ps a P + a w1 := ps_insert a P w1 (hPW w1 hw1)
  have hC2L : ∀ i, C2 i = true → avail (L ++ lst C1) i = true := by
    intro i h
    simp only [C2, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact hPL1 i h
    · subst h; exact hW1 _ hw1
  have hUge : ps a T + a w1 ≤ ps a U := by
    have hTw1 : T w1 = false := by
      cases ht : T w1
      · rfl
      · have := hTW w1 ht; rw [hw1] at this; cases this
    rw [← ps_insert a T w1 hTw1]
    apply ps_mono; intro i h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · simp [U, h]
    · subst h; simp [U, hw1]
  have big1 : B ≤ ps a (avail (L ++ lst C1)) := by
    have := hTw w1 hw1
    omega
  have hC2eq : ps a C2 = B := by
    apply maxExact a B run1 nost big1 C2 hC2L _ (by omega)
    intro i hav hc
    simp only [C2, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    rcases rest1 i hav with h | h
    · have := hWW w1 i hw1 h (fun e => hc.2 e.symm)
      omega
    · have := hPmax i h hc.1
      omega
  have run2 := run_exact a B run1 C2 hC2L hC2eq
  have cl2 := ps_avail_close a (L ++ lst C1) C2 hC2L
  have av2 : ∀ i, avail (L ++ lst C1 ++ lst C2) i = (avail (L ++ lst C1) i && !C2 i) :=
    avail_append (L ++ lst C1) C2
  -- the fired part that is left after the two blocks
  let F3 : Fin k → Bool := fun i => avail (L ++ lst C1 ++ lst C2) i && !U i
  have f2split := ps_split a F2 P
  have f21 : ps a (fun i => F2 i && P i) = ps a P := by
    apply ps_congr; intro i
    cases hp : P i
    · simp
    · simp [hPF2 i hp]
  have f22 : ps a (fun i => F2 i && !P i) = ps a F3 := by
    apply ps_congr; intro i
    simp only [F2, F3, av2, C2]
    by_cases e : i = w1
    · subst e; simp [U, hw1]
    · cases avail (L ++ lst C1) i <;> cases P i <;> cases U i <;> simp [e]
  have total : ps a (Fp L U) = (B - ps a T) + (B - a w1) + ps a F3 := by omega
  have hF3F : ∀ i, F3 i = true → F2 i = true ∧ P i = false := by
    intro i h
    simp only [F3, av2, C2, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at h
    exact ⟨by simp [F2, h.1.1, h.2], h.1.2.1⟩
  -- Stage 3
  by_cases hF3 : ∀ i, F3 i = false
  · have hF3z : ps a F3 = 0 := ps_zero a F3 hF3
    have := hTw w1 hw1
    omega
  obtain ⟨f, hf⟩ : ∃ f, F3 f = true := by
    apply Classical.byContradiction
    intro hno
    exact hF3 (fun i => by
      cases h : F3 i
      · rfl
      · exact absurd ⟨i, h⟩ hno)
  have hfL2 : avail (L ++ lst C1 ++ lst C2) f = true := by
    simp only [F3, Bool.and_eq_true] at hf; exact hf.1
  obtain ⟨P3, -, hP3F3, hP3B, hP3max⟩ :=
    exists_maximal a B apos F3 _ (fun _ => false) (Nat.le_refl _) (fun i h => by simp at h)
      (by rw [ps_zero a _ (fun _ => rfl)]; exact Nat.zero_le _)
  have hP3F : ∀ i, P3 i = true → Fp L U i = true := fun i h => hF2F i (hF3F i (hP3F3 i h)).1
  have hP3lt : ps a P3 < B := by have := noexact P3 hP3F; omega
  -- some bundle g of P3, and it is larger than w1
  have hfB : a f ≤ B := by
    apply Classical.byContradiction
    intro h
    have hfnot : f ∉ L ++ lst C1 ++ lst C2 := by simpa [avail] using hfL2
    exact nost (stuck_of_oversize a B apos Bpos f (by omega) _ _ (Nat.le_refl _) run2 hfnot)
  obtain ⟨g, hg⟩ : ∃ g, P3 g = true := by
    cases hp : P3 f
    · have := hP3max f hf hp
      exact exists_of_ps_pos a P3 (by omega)
    · exact ⟨f, hp⟩
  have hgF3 := hF3F g (hP3F3 g hg)
  have hgbig : a w1 < a g := by
    have := hPmax g hgF3.1 hgF3.2
    omega
  have hgP3 := ps_ge a P3 g hg
  have hP3L2 : ∀ i, P3 i = true → avail (L ++ lst C1 ++ lst C2) i = true := by
    intro i h
    have := hP3F3 i h
    simp only [F3, Bool.and_eq_true] at this
    exact this.1
  -- P3 is maximal among everything left, so it must be everything left
  have hall : ∀ i, avail (L ++ lst C1 ++ lst C2) i = true → P3 i = true := by
    intro i hav
    apply Classical.byContradiction
    intro hp
    have hp' : P3 i = false := by simpa using hp
    apply nost
    apply stuck_of_maximal a B run2 P3 hP3L2 hP3lt _ ⟨i, hav, hp'⟩
    intro j hj hpj
    cases hu : U j
    · have : F3 j = true := by
        show (avail (L ++ lst C1 ++ lst C2) j && !U j) = true
        rw [hj, hu]; rfl
      exact hP3max j this hpj
    · have hwj : W j = true := by
        simp only [U, Bool.or_eq_true] at hu
        rcases hu with h | h
        · rw [av2, av1] at hj; simp [hTC1 j h] at hj
        · exact h
      have hj1 : j ≠ w1 := by
        intro e; subst e
        rw [av2] at hj; simp [C2] at hj
      have := hWW w1 j hw1 hwj (fun e => hj1 e.symm)
      omega
  have hF3P3 : ps a F3 ≤ ps a P3 := by
    apply ps_mono; intro i h
    simp only [F3, Bool.and_eq_true] at h
    exact hall i h.1
  obtain ⟨u, huU, hRu⟩ := room a B apos run nost big U noexact P3 hP3F (by omega)
  have w := wit u huU
  have := apos u
  have hT := hTw w1 hw1
  have FB : ps a (Fp L U) < B + B := by omega
  have hmod := mod_of_two B (ps a (Fp L U)) Bpos Fbig FB
  omega

/-! ## Consequences at the start state -/

theorem ps_compl (U : Fin k → Bool) : ps a (fun i => !U i) = tot a - ps a U := by
  have h := ps_split a (fun _ => true) U
  have e1 : ps a (fun i => true && U i) = ps a U := ps_congr a (fun i => by simp)
  have e2 : ps a (fun i => true && !U i) = ps a (fun i => !U i) := ps_congr a (fun i => by simp)
  simp only [tot]; omega

theorem ps_or_disjoint (T W : Fin k → Bool) (h : ∀ i, T i = true → W i = false) :
    ps a (fun i => T i || W i) = ps a T + ps a W := by
  rw [ps_split a (fun i => T i || W i) T]
  have e1 : ps a (fun i => (T i || W i) && T i) = ps a T := ps_congr a (fun i => by cases T i <;> simp)
  have e2 : ps a (fun i => (T i || W i) && !T i) = ps a W := by
    apply ps_congr; intro i
    cases ht : T i
    · simp
    · simp [h i ht]
  omega

/-- A split witness at the start, stated with the total. -/
theorem bad_of_split (apos : ∀ i, 0 < a i) (Bpos : 0 < B) (T W : Fin k → Bool)
    (hTW : ∀ i, T i = true → W i = false) (hne : ∃ u, T u = true ∨ W u = true)
    (hTB : ps a T ≤ B) (hTw : ∀ w, W w = true → B < ps a T + a w)
    (hWW : ∀ w w', W w = true → W w' = true → w ≠ w' → B < a w + a w')
    (wit : ∀ u, (T u || W u) = true → B < (tot a - ps a T - ps a W) % B + a u) :
    ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  apply (bad_terminal_reachable_iff a B apos).mpr
  have hF : ps a (Fp [] (fun i => T i || W i)) = tot a - ps a T - ps a W := by
    rw [ps_congr a (fun i => by simp [Fp, avail_nil] : ∀ i, Fp [] (fun i => T i || W i) i = !(T i || W i)),
      ps_compl, ps_or_disjoint a T W hTW]
    omega
  exact realise_split a B apos Bpos _ [] (Nat.le_refl _) Run.nil T W (fun i _ => avail_nil i)
    (fun i _ => avail_nil i) hTW hne hTB hTw hWW (fun u hu => by rw [hF]; exact wit u hu)

/-- **Three unfired senders.**  A witness leaving exactly three senders unfired
(each bundle at most `B`) is realised. -/
theorem bad_of_triple (apos : ∀ i, 0 < a i) (Bpos : 0 < B) (u v w : Fin k)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hu : a u ≤ B) (hv : a v ≤ B) (hw : a w ≤ B)
    (wu : B < (tot a - a u - a v - a w) % B + a u) (wv : B < (tot a - a u - a v - a w) % B + a v)
    (ww : B < (tot a - a u - a v - a w) % B + a w) :
    ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  -- a pair as T and the third as W, or one as T and the other two as W
  have sing : ∀ x : Fin k, ps a (fun j => decide (j = x)) = a x := ps_single a
  have pair_T : ∀ x y z : Fin k, x ≠ y → x ≠ z → y ≠ z →
      (∀ c, c = x ∨ c = y ∨ c = z → B < (tot a - a x - a y - a z) % B + a c) →
      a x + a y ≤ B → B < a x + a y + a z →
      ∃ y', Reaches (Step a B) (stateOf a [] 0) y' ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y' ∧ ¬ OrdinaryStable (out a B) y' := by
    intro x y z hxy hxz hyz wc hfit hover
    have hp := ps_pair a hxy
    apply bad_of_split a B apos Bpos (pairP x y) (fun j => decide (j = z))
    · intro i hi; rcases (pairP_iff x y i).mp hi with e | e <;> subst e <;> simp [hxz, hyz]
    · exact ⟨x, Or.inl ((pairP_iff x y x).mpr (Or.inl rfl))⟩
    · omega
    · intro c hc; simp only [decide_eq_true_eq] at hc; subst hc; omega
    · intro c c' hc hc' hne'; simp only [decide_eq_true_eq] at hc hc'; subst hc; subst hc'
      exact absurd rfl hne'
    · intro c hc
      rw [hp, sing]
      have : tot a - (a x + a y) - a z = tot a - a x - a y - a z := by omega
      rw [this]
      apply wc
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · rcases (pairP_iff x y c).mp hc with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr hc)
  have wc : ∀ c, c = u ∨ c = v ∨ c = w → B < (tot a - a u - a v - a w) % B + a c := by
    intro c hc; rcases hc with e | e | e <;> subst e <;> assumption
  by_cases hsmall : a u + a v + a w ≤ B
  · -- the whole triple is small: T = triple, W = ∅
    have hp := ps_pair a huv
    have hpw : (pairP u v) w = false := by
      simp only [pairP, Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨fun e => huw e.symm, fun e => hvw e.symm⟩
    have hins := ps_insert a (pairP u v) w hpw
    apply bad_of_split a B apos Bpos (fun j => pairP u v j || decide (j = w)) (fun _ => false)
    · intro _ _; rfl
    · exact ⟨u, Or.inl (by simp [pairP])⟩
    · rw [hins, hp]; omega
    · intro c hc; cases hc
    · intro c _ hc; cases hc
    · intro c hc
      rw [hins, hp, ps_zero a _ (fun _ => rfl)]
      have : tot a - (a u + a v + a w) - 0 = tot a - a u - a v - a w := by omega
      rw [this]
      apply wc
      simp only [Bool.or_false, Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · rcases (pairP_iff u v c).mp hc with e | e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr hc)
  · by_cases h1 : a u + a v ≤ B
    · exact pair_T u v w huv huw hvw wc h1 (by omega)
    by_cases h2 : a u + a w ≤ B
    · have eq : tot a - a u - a w - a v = tot a - a u - a v - a w := by omega
      exact pair_T u w v huw huv (fun e => hvw e.symm)
        (fun c hc => by rw [eq]; exact wc c (by rcases hc with e | e | e <;> simp [e])) h2 (by omega)
    by_cases h3 : a v + a w ≤ B
    · have eq : tot a - a v - a w - a u = tot a - a u - a v - a w := by omega
      exact pair_T v w u hvw (fun e => huv e.symm) (fun e => huw e.symm)
        (fun c hc => by rw [eq]; exact wc c (by rcases hc with e | e | e <;> simp [e])) h3 (by omega)
    -- no pair fits: T = {u}, W = {v, w}
    have hp := ps_pair a hvw
    apply bad_of_split a B apos Bpos (fun j => decide (j = u)) (pairP v w)
    · intro i hi; simp only [decide_eq_true_eq] at hi; subst hi; simp [pairP, huv, huw]
    · exact ⟨u, Or.inl (by simp)⟩
    · rw [sing]; exact hu
    · intro c hc; rw [sing]
      rcases (pairP_iff v w c).mp hc with e | e <;> subst e <;> omega
    · intro c c' hc hc' hne'
      rcases (pairP_iff v w c).mp hc with e | e <;> rcases (pairP_iff v w c').mp hc' with e' | e' <;>
        subst e <;> subst e' <;> first | exact absurd rfl hne' | omega
    · intro c hc
      rw [sing, hp]
      have : tot a - a u - (a v + a w) = tot a - a u - a v - a w := by omega
      rw [this]
      apply wc
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | hc
      · exact Or.inl hc
      · rcases (pairP_iff v w c).mp hc with e | e
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr e)

/-- **A witness whose fired part fits in one bin** is realised: fire it. -/
theorem bad_of_onebin (apos : ∀ i, 0 < a i) (U : Fin k → Bool) (hne : ∃ u, U u = true)
    (hF : ps a (fun i => !U i) < B)
    (wit : ∀ u, U u = true → B < ps a (fun i => !U i) % B + a u) :
    ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  apply (bad_terminal_reachable_iff a B apos).mpr
  apply stuck_of_maximal a B Run.nil (fun i => !U i) (fun i _ => avail_nil i) hF
  · intro i _ hs
    have hu : U i = true := by simpa using hs
    have := wit i hu
    rw [Nat.mod_eq_of_lt hF] at this
    exact this
  · obtain ⟨u, hu⟩ := hne
    exact ⟨u, avail_nil u, by simp [hu]⟩

/-! ## The classifier with three-sender witnesses -/

def dpBadT : Bool :=
  dpBad a B ||
  (List.finRange k).any (fun u => (List.finRange k).any (fun v => (List.finRange k).any (fun w =>
    decide (u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ a u ≤ B ∧ a v ≤ B ∧ a w ≤ B ∧
      B < (tot a - a u - a v - a w) % B + a u ∧ B < (tot a - a u - a v - a w) % B + a v ∧
      B < (tot a - a u - a v - a w) % B + a w))))

theorem bad_of_dpBadT (apos : ∀ i, 0 < a i) (Bpos : 0 < B) (h : dpBadT a B = true) :
    ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  simp only [dpBadT, Bool.or_eq_true] at h
  rcases h with h | h
  · exact bad_of_dpBad a B apos Bpos h
  · simp only [List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at h
    obtain ⟨u, v, w, huv, huw, hvw, hu, hv, hw, wu, wv, ww⟩ := h
    exact bad_of_triple a B apos Bpos u v w huv huw hvw hu hv hw wu wv ww

def classifyT : Verdict :=
  if dpFast a B = false then .safe else if dpBadT a B = true then .bad else .unknown

theorem classifyT_safe (apos : ∀ i, 0 < a i) (Bpos : 0 < B) (h : classifyT a B = .safe) :
    ¬ ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  unfold classifyT at h
  split at h
  · exact safe_of_dpFast a B apos Bpos (by assumption)
  · split at h <;> cases h

theorem classifyT_bad (apos : ∀ i, 0 < a i) (Bpos : 0 < B) (h : classifyT a B = .bad) :
    ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  unfold classifyT at h
  split at h
  · cases h
  · split at h
    · exact bad_of_dpBadT a B apos Bpos (by assumption)
    · cases h

end Star

end CBMDFixedState
