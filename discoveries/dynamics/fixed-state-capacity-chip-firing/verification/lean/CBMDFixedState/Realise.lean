import CBMDFixedState.Stuck

/-!
# A residue witness with a small unfired total is realised

`Stuck.lean` proves that a stuck bin run yields a residue witness.  This module
proves a partial converse: **if some residue witness leaves unfired senders of
total at most `B`, then some bin run gets stuck** (`realise_small`).

Sets of senders are Boolean predicates on `Fin k`; `ps P` is the total of the
bundles in `P`.  The proof is by strong induction on the total of the senders
not yet fired, starting from any reachable state with empty receiver.  Assuming
no run gets stuck, the witness's fired part `F` has no subset of total exactly
`B` (else close that block and recurse), has total at least `B` (else firing it
already gets stuck), and every sub-`B` subset of `F` leaves room for some
unfired bundle (extend it to a maximal one-bin packing, which must be exact).
Packing the unfired part first and closing its block exactly then leaves too
little of `F` to account for its residue.
-/

namespace CBMDFixedState

namespace Star

variable {k : Nat} (a : Fin k → Nat) (B : Nat)

/-! ## Sets of senders as predicates -/

def lst (P : Fin k → Bool) : List (Fin k) := (List.finRange k).filter P

def ps (P : Fin k → Bool) : Nat := lsum a (lst P)

theorem mem_lst (P : Fin k → Bool) (i : Fin k) : i ∈ lst P ↔ P i = true := by
  simp [lst, List.mem_filter, List.mem_finRange]

theorem lst_nodup (P : Fin k → Bool) : (lst P).Nodup :=
  (List.nodup_finRange k).filter P

theorem lsum_filter_split (P Q : Fin k → Bool) : ∀ l : List (Fin k),
    lsum a (l.filter P) =
      lsum a (l.filter (fun i => P i && Q i)) + lsum a (l.filter (fun i => P i && !Q i))
  | [] => by simp
  | x :: l => by
    have ih := lsum_filter_split P Q l
    cases hp : P x <;> cases hq : Q x <;> simp [hp, hq, ih] <;> omega

theorem ps_split (P Q : Fin k → Bool) :
    ps a P = ps a (fun i => P i && Q i) + ps a (fun i => P i && !Q i) :=
  lsum_filter_split a P Q _

theorem ps_congr {P Q : Fin k → Bool} (h : ∀ i, P i = Q i) : ps a P = ps a Q := by
  have : P = Q := funext h
  subst this; rfl

theorem ps_mono {P Q : Fin k → Bool} (h : ∀ i, P i = true → Q i = true) : ps a P ≤ ps a Q := by
  rw [ps_split a Q P]
  have : ps a (fun i => Q i && P i) = ps a P := by
    apply ps_congr; intro i
    cases hp : P i <;> cases hq : Q i <;> simp_all
  omega

theorem lsum_filter_ge (P : Fin k → Bool) (i : Fin k) (hi : P i = true) :
    ∀ l : List (Fin k), i ∈ l → a i ≤ lsum a (l.filter P)
  | [], h => by simp at h
  | x :: l, h => by
    by_cases e : x = i
    · subst e; simp [hi]
    · have m : i ∈ l := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm e
        · exact h
      have := lsum_filter_ge P i hi l m
      cases hx : P x <;> simp [hx] <;> omega

theorem ps_ge (P : Fin k → Bool) (i : Fin k) (hi : P i = true) : a i ≤ ps a P :=
  lsum_filter_ge a P i hi _ (List.mem_finRange i)

theorem ps_zero (P : Fin k → Bool) (h : ∀ i, P i = false) : ps a P = 0 := by
  have : lst P = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i hi
    rw [mem_lst] at hi
    simp [h i] at hi
  simp [ps, this]

theorem exists_of_ps_pos (P : Fin k → Bool) (h : 0 < ps a P) : ∃ i, P i = true := by
  apply Classical.byContradiction
  intro hn
  have : ps a P = 0 := ps_zero a P (fun i => by
    cases hp : P i
    · rfl
    · exact absurd ⟨i, hp⟩ hn)
  omega

theorem lsum_filter_eq_single (i : Fin k) : ∀ l : List (Fin k), l.Nodup →
    lsum a (l.filter (fun j => decide (j = i))) = if i ∈ l then a i else 0
  | [], _ => by simp
  | x :: l, nd => by
    have nd' : l.Nodup := (List.nodup_cons.mp nd).2
    have nx : x ∉ l := (List.nodup_cons.mp nd).1
    have ih := lsum_filter_eq_single i l nd'
    by_cases e : x = i
    · subst e
      simp [ih, nx]
    · by_cases m : i ∈ l
      · simp [e, ih, m]
      · have : ¬ (i = x) := fun h => e h.symm
        simp [e, ih, m, this]

theorem ps_single (i : Fin k) : ps a (fun j => decide (j = i)) = a i := by
  have := lsum_filter_eq_single a i (List.finRange k) (List.nodup_finRange k)
  simpa [ps, lst, List.mem_finRange] using this

/-! ## Runs that fire a set -/

def avail (L : List (Fin k)) : Fin k → Bool := fun i => decide (i ∉ L)

theorem avail_append (L : List (Fin k)) (S : Fin k → Bool) (i : Fin k) :
    avail (L ++ lst S) i = (avail L i && !S i) := by
  simp only [avail, List.mem_append, mem_lst]
  cases hS : S i <;> by_cases m : i ∈ L <;> simp [m]

theorem run_add_set {L : List (Fin k)} {f : Nat} (r : Run a B L f) (S : Fin k → Bool)
    (hS : ∀ i, S i = true → i ∉ L) (fits : f + ps a S ≤ B) :
    Run a B (L ++ lst S) (f + ps a S) := by
  apply run_extend a B (lst S) r _ fits
  rw [List.nodup_append]
  refine ⟨run_nodup a B r, lst_nodup S, ?_⟩
  intro x hx y hy e
  subst e
  exact hS x ((mem_lst S x).mp hy) hx

/-- Some bin run gets stuck. -/
def Stuck : Prop :=
  ∃ L f, Run a B L f ∧ f < B ∧ (∃ i, i ∉ L) ∧ ∀ i, i ∉ L → B < f + a i

/-- From an empty receiver, firing a set that leaves the receiver short of full
while every other unfired bundle overflows is a stuck run. -/
theorem stuck_of_maximal {L : List (Fin k)} (r : Run a B L 0) (S : Fin k → Bool)
    (hS : ∀ i, S i = true → avail L i = true) (lt : ps a S < B)
    (maxl : ∀ i, avail L i = true → S i = false → B < ps a S + a i)
    (rest : ∃ i, avail L i = true ∧ S i = false) : Stuck a B := by
  have hS' : ∀ i, S i = true → i ∉ L := fun i h => by simpa [avail] using hS i h
  have run := run_add_set a B r S hS' (by omega)
  rw [Nat.zero_add] at run
  refine ⟨L ++ lst S, ps a S, run, lt, ?_, ?_⟩
  · obtain ⟨i, hi, hs⟩ := rest
    exact ⟨i, by
      have := avail_append L S i
      simp [hi, hs] at this
      simpa [avail] using this⟩
  · intro i hi
    have := avail_append L S i
    have hav : avail (L ++ lst S) i = true := by simpa [avail] using hi
    rw [this] at hav
    simp at hav
    exact maxl i hav.1 hav.2

/-- Firing a set of total exactly `B` from an empty receiver returns to an empty receiver. -/
theorem run_exact {L : List (Fin k)} (r : Run a B L 0) (S : Fin k → Bool)
    (hS : ∀ i, S i = true → avail L i = true) (ex : ps a S = B) :
    Run a B (L ++ lst S) 0 := by
  have hS' : ∀ i, S i = true → i ∉ L := fun i h => by simpa [avail] using hS i h
  have run := run_add_set a B r S hS' (by omega)
  rw [Nat.zero_add, ex] at run
  exact Run.reset run

/-- **Maximal extension** inside a pool. -/
theorem exists_maximal (apos : ∀ i, 0 < a i) (P : Fin k → Bool) :
    ∀ (n : Nat) (S : Fin k → Bool), ps a (fun i => P i && !S i) ≤ n →
      (∀ i, S i = true → P i = true) → ps a S ≤ B →
      ∃ G : Fin k → Bool, (∀ i, S i = true → G i = true) ∧ (∀ i, G i = true → P i = true) ∧
        ps a G ≤ B ∧ ∀ i, P i = true → G i = false → B < ps a G + a i := by
  intro n
  induction n with
  | zero =>
    intro S hn hSP hS
    refine ⟨S, fun i h => h, hSP, hS, ?_⟩
    intro i hP hG
    have := ps_ge a (fun i => P i && !S i) i (by simp [hP, hG])
    have := apos i
    omega
  | succ n ih =>
    intro S hn hSP hS
    by_cases h : ∃ i, P i = true ∧ S i = false ∧ ps a S + a i ≤ B
    · obtain ⟨i, hP, hSi, fit⟩ := h
      let S' : Fin k → Bool := fun j => S j || decide (j = i)
      have sum' : ps a S' = ps a S + a i := by
        rw [ps_split a S' S]
        have e1 : ps a (fun j => S' j && S j) = ps a S := by
          apply ps_congr; intro j; simp only [S']; cases S j <;> simp
        have e2 : ps a (fun j => S' j && !S j) = ps a (fun j => decide (j = i)) := by
          apply ps_congr; intro j; simp only [S']
          by_cases e : j = i
          · subst e; simp [hSi]
          · cases hs : S j <;> simp [e]
        rw [e1, e2, ps_single]
      have dec : ps a (fun j => P j && !S' j) + a i = ps a (fun j => P j && !S j) := by
        rw [ps_split a (fun j => P j && !S j) (fun j => decide (j = i))]
        have e1 : ps a (fun j => (P j && !S j) && decide (j = i)) = a i := by
          rw [← ps_single a i]; apply ps_congr; intro j
          by_cases e : j = i
          · subst e; simp [hP, hSi]
          · simp [e]
        have e2 : ps a (fun j => (P j && !S j) && !decide (j = i)) = ps a (fun j => P j && !S' j) := by
          apply ps_congr; intro j; simp only [S']
          cases P j <;> cases S j <;> simp
        omega
      have := apos i
      obtain ⟨G, h1, h2, h3, h4⟩ := ih S' (by omega)
        (fun j hj => by
          simp only [S', Bool.or_eq_true, decide_eq_true_eq] at hj
          rcases hj with hj | hj
          · exact hSP j hj
          · subst hj; exact hP)
        (by omega)
      exact ⟨G, fun j hj => h1 j (by simp [S', hj]), h2, h3, h4⟩
    · refine ⟨S, fun i h => h, hSP, hS, ?_⟩
      intro i hP hG
      apply Classical.byContradiction
      intro hle
      exact h ⟨i, hP, hG, by omega⟩

/-! ## The partial converse -/

theorem mod_of_two (x : Nat) (Bpos : 0 < B) (h1 : B ≤ x) (h2 : x < B + B) : x % B = x - B := by
  rw [Nat.mod_eq_sub_mod h1]
  exact Nat.mod_eq_of_lt (by omega)

theorem ps_insert (P : Fin k → Bool) (i : Fin k) (h : P i = false) :
    ps a (fun j => P j || decide (j = i)) = ps a P + a i := by
  rw [ps_split a _ P]
  have e1 : ps a (fun j => (P j || decide (j = i)) && P j) = ps a P := by
    apply ps_congr; intro j; cases P j <;> simp
  have e2 : ps a (fun j => (P j || decide (j = i)) && !P j) = ps a (fun j => decide (j = i)) := by
    apply ps_congr; intro j
    by_cases e : j = i
    · subst e; simp [h]
    · cases hs : P j <;> simp [e]
  rw [e1, e2, ps_single]

/-- The fired part of a witness: available and not in `U`. -/
def Fp (L : List (Fin k)) (U : Fin k → Bool) : Fin k → Bool := fun i => avail L i && !U i

theorem Fp_avail {L : List (Fin k)} {U : Fin k → Bool} {i : Fin k} (h : Fp L U i = true) :
    avail L i = true := by
  simp only [Fp, Bool.and_eq_true] at h; exact h.1

theorem Fp_notU {L : List (Fin k)} {U : Fin k → Bool} {i : Fin k} (h : Fp L U i = true) :
    U i = false := by
  simp only [Fp, Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2

theorem ps_avail_split (L : List (Fin k)) (U : Fin k → Bool)
    (hUL : ∀ u, U u = true → avail L u = true) :
    ps a (avail L) = ps a U + ps a (Fp L U) := by
  rw [ps_split a (avail L) U]
  have : ps a (fun i => avail L i && U i) = ps a U := by
    apply ps_congr; intro i
    cases hu : U i
    · simp
    · simp [hUL i hu]
  rw [this]; rfl

/-- Closing an exact block `C` inside the available senders. -/
theorem ps_avail_close (L : List (Fin k)) (C : Fin k → Bool)
    (hC : ∀ i, C i = true → avail L i = true) :
    ps a (avail L) = ps a C + ps a (avail (L ++ lst C)) := by
  rw [ps_split a (avail L) C]
  have e1 : ps a (fun i => avail L i && C i) = ps a C := by
    apply ps_congr; intro i
    cases hc : C i
    · simp
    · simp [hC i hc]
  have e2 : ps a (fun i => avail L i && !C i) = ps a (avail (L ++ lst C)) :=
    ps_congr a (fun i => (avail_append L C i).symm)
  rw [e1, e2]

/-- (2) Without a stuck run, the fired part of a witness totals at least `B`. -/
theorem fbig {L : List (Fin k)} (run : Run a B L 0) (U : Fin k → Bool)
    (hne : ∃ u, U u = true) (hUL : ∀ u, U u = true → avail L u = true)
    (wit : ∀ u, U u = true → B < ps a (Fp L U) % B + a u) (nost : ¬ Stuck a B) :
    B ≤ ps a (Fp L U) := by
  apply Classical.byContradiction
  intro hlt
  apply nost
  apply stuck_of_maximal a B run (Fp L U) (fun i h => Fp_avail h) (by omega)
  · intro i hav hFi
    have hU : U i = true := by simp [Fp, hav] at hFi; exact hFi
    have w := wit i hU
    rw [Nat.mod_eq_of_lt (by omega)] at w
    exact w
  · obtain ⟨u, hu⟩ := hne
    exact ⟨u, hUL u hu, by simp [Fp, hu]⟩

/-- Without a stuck run, every maximal one-bin packing from an empty receiver is exact. -/
theorem maxExact {L : List (Fin k)} (run : Run a B L 0) (nost : ¬ Stuck a B)
    (big : B ≤ ps a (avail L)) (C : Fin k → Bool) (hC : ∀ i, C i = true → avail L i = true)
    (maxl : ∀ i, avail L i = true → C i = false → B < ps a C + a i) (hle : ps a C ≤ B) :
    ps a C = B := by
  apply Classical.byContradiction
  intro hne'
  apply nost
  apply stuck_of_maximal a B run C hC (by omega) maxl
  apply Classical.byContradiction
  intro hall
  have sub : ∀ i, avail L i = true → C i = true := by
    intro i hi
    cases hc : C i
    · exact absurd ⟨i, hi, hc⟩ hall
    · rfl
  have := ps_mono a sub
  omega

/-- (3) Without a stuck run, and with no exact block inside the fired part, every
sub-`B` subset of the fired part leaves room for some bundle of `U`. -/
theorem room (apos : ∀ i, 0 < a i) {L : List (Fin k)} (run : Run a B L 0) (nost : ¬ Stuck a B)
    (big : B ≤ ps a (avail L)) (U : Fin k → Bool)
    (noexact : ∀ E : Fin k → Bool, (∀ i, E i = true → Fp L U i = true) → ps a E ≠ B)
    (S : Fin k → Bool) (hSF : ∀ i, S i = true → Fp L U i = true) (hSB : ps a S ≤ B) :
    ∃ u, U u = true ∧ ps a S + a u ≤ B := by
  obtain ⟨G, hSG, hGF, hGB, hGmax⟩ :=
    exists_maximal a B apos (Fp L U) _ S (Nat.le_refl _) hSF hSB
  have hGlt : ps a G < B := by
    have := noexact G hGF; omega
  obtain ⟨C, hGC, hCL, hCB, hCmax⟩ :=
    exists_maximal a B apos (avail L) _ G (Nat.le_refl _) (fun i h => Fp_avail (hGF i h)) hGB
  have hCeq := maxExact a B run nost big C hCL hCmax hCB
  have csplit := ps_split a C G
  have cg : ps a (fun i => C i && G i) = ps a G := by
    apply ps_congr; intro i
    cases hg : G i
    · simp
    · simp [hGC i hg]
  have hpos : 0 < ps a (fun i => C i && !G i) := by omega
  obtain ⟨u, hu⟩ := exists_of_ps_pos a _ hpos
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hu
  have hau : a u ≤ ps a (fun i => C i && !G i) := ps_ge a _ u (by simp [hu.1, hu.2])
  have huU : U u = true := by
    apply Classical.byContradiction
    intro hnu
    have hFu : Fp L U u = true := by simp [Fp, hCL u hu.1]; simpa using hnu
    have := hGmax u hFu hu.2
    omega
  refine ⟨u, huU, ?_⟩
  have := ps_mono a hSG
  omega

/-- Without a stuck run, if the available senders contain no exact block, they total less than `B`. -/
theorem small_rest (apos : ∀ i, 0 < a i) {L : List (Fin k)} (run : Run a B L 0)
    (nost : ¬ Stuck a B)
    (noex : ∀ E : Fin k → Bool, (∀ i, E i = true → avail L i = true) → ps a E ≠ B) :
    ps a (avail L) < B := by
  obtain ⟨G0, -, hG0R, hG0B, hG0max⟩ :=
    exists_maximal a B apos (avail L) _ (fun _ => false) (Nat.le_refl _) (fun i h => by simp at h)
      (by rw [ps_zero a _ (fun _ => rfl)]; exact Nat.zero_le _)
  have hG0lt : ps a G0 < B := by
    have := noex G0 hG0R; omega
  have hsub : ∀ i, avail L i = true → G0 i = true := by
    intro i hi
    apply Classical.byContradiction
    intro hg
    have hg' : G0 i = false := by simpa using hg
    exact nost (stuck_of_maximal a B run G0 hG0R hG0lt hG0max ⟨i, hi, hg'⟩)
  have := ps_mono a hsub
  omega

/-- Closing an exact block inside the fired part keeps the witness. -/
theorem witness_after_block {L : List (Fin k)} (U E : Fin k → Bool)
    (hEF : ∀ i, E i = true → Fp L U i = true) (hEB : ps a E = B)
    (wit : ∀ u, U u = true → B < ps a (Fp L U) % B + a u) :
    (∀ u, U u = true → avail L u = true → avail (L ++ lst E) u = true) ∧
      ∀ u, U u = true → B < ps a (Fp (L ++ lst E) U) % B + a u := by
  constructor
  · intro u hu hav
    rw [avail_append]
    have hEu : E u = false := by
      cases he : E u
      · rfl
      · have := Fp_notU (hEF u he); simp [hu] at this
    simp [hav, hEu]
  · intro u hu
    have w := wit u hu
    have Fsplit := ps_split a (Fp L U) E
    have f1 : ps a (fun i => Fp L U i && E i) = B := by
      rw [← hEB]; apply ps_congr; intro i
      cases he : E i
      · simp
      · simp [hEF i he]
    have f2 : ps a (fun i => Fp L U i && !E i) = ps a (Fp (L ++ lst E) U) := by
      apply ps_congr; intro i; simp only [Fp]; rw [avail_append]
      cases avail L i <;> cases E i <;> cases U i <;> simp
    have : ps a (Fp L U) % B = ps a (Fp (L ++ lst E) U) % B := by
      rw [Fsplit, f1, f2, Nat.add_mod_left]
    omega

/-- **A residue witness whose unfired senders total at most `B` is realised.**
From any reachable state with an empty receiver: if `U` is a nonempty set of
available senders of total at most `B`, and every sender of `U` overflows on
top of the residue of the other available senders' total, then some bin run
gets stuck. -/
theorem realise_small (apos : ∀ i, 0 < a i) (Bpos : 0 < B) :
    ∀ (n : Nat) (L : List (Fin k)), ps a (avail L) ≤ n → Run a B L 0 →
      ∀ U : Fin k → Bool, (∃ u, U u = true) → (∀ u, U u = true → avail L u = true) →
        ps a U ≤ B → (∀ u, U u = true → B < ps a (Fp L U) % B + a u) →
        Stuck a B := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro L hn run U hne hUL hUB wit
  apply Classical.byContradiction
  intro nost
  -- (1) no subset of the fired part has total exactly B
  have noexact : ∀ E : Fin k → Bool, (∀ i, E i = true → Fp L U i = true) → ps a E ≠ B := by
    intro E hEF hEB
    have run' := run_exact a B run E (fun i h => Fp_avail (hEF i h)) hEB
    have cl := ps_avail_close a L E (fun i h => Fp_avail (hEF i h))
    obtain ⟨hav, wit'⟩ := witness_after_block a B U E hEF hEB wit
    exact nost (ih _ (by omega) _ (Nat.le_refl _) run' U hne (fun u hu => hav u hu (hUL u hu))
      hUB wit')
  have Fbig := fbig a B run U hne hUL wit nost
  have split := ps_avail_split a L U hUL
  have big : B ≤ ps a (avail L) := by omega
  -- (4) pack U first; its maximal extension E is exact
  obtain ⟨E, hUE, hEL, hEB, hEmax⟩ :=
    exists_maximal a B apos (avail L) _ U (Nat.le_refl _) hUL hUB
  have hEeq := maxExact a B run nost big E hEL hEmax hEB
  have run' := run_exact a B run E hEL hEeq
  -- (5) what is left lies in the fired part, so it is exact-free, small, and leaves room
  have restF : ∀ i, avail (L ++ lst E) i = true → Fp L U i = true := by
    intro i h
    rw [avail_append] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    have hu : U i = false := by
      cases hu : U i
      · rfl
      · simp [hUE i hu] at h
    simp [Fp, h.1, hu]
  have restlt := small_rest a B apos run' nost (fun E' hE' => noexact E' (fun i h => restF i (hE' i h)))
  obtain ⟨u, huU, hRu⟩ := room a B apos run nost big U noexact _ restF (by omega)
  -- (6) count
  have cl := ps_avail_close a L E hEL
  have esplit := ps_split a E U
  have eu : ps a (fun i => E i && U i) = ps a U := by
    apply ps_congr; intro i
    cases hu : U i
    · simp
    · simp [hUE i hu]
  have hUu := ps_ge a U u huU
  have w := wit u huU
  have := apos u
  have FB : ps a (Fp L U) < B + B := by omega
  have hmod := mod_of_two B (ps a (Fp L U)) Bpos Fbig FB
  omega

def pairP (u v : Fin k) : Fin k → Bool := fun i => decide (i = u) || decide (i = v)

theorem pairP_iff (u v i : Fin k) : pairP u v i = true ↔ (i = u ∨ i = v) := by
  simp [pairP]

theorem ps_pair {u v : Fin k} (huv : u ≠ v) : ps a (pairP u v) = a u + a v := by
  have := ps_insert a (fun j => decide (j = u)) v (by simp; exact fun h => huv h.symm)
  rw [ps_single] at this
  exact this

/-- **A residue witness with two unfired senders is realised.** -/
theorem realise_pair (apos : ∀ i, 0 < a i) (Bpos : 0 < B) :
    ∀ (n : Nat) (L : List (Fin k)), ps a (avail L) ≤ n → Run a B L 0 →
      ∀ u v : Fin k, u ≠ v → avail L u = true → avail L v = true →
        (∀ x, pairP u v x = true → B < ps a (Fp L (pairP u v)) % B + a x) →
        Stuck a B := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro L hn run u v huv hu hv wit
  let U := pairP u v
  have wit : ∀ x, U x = true → B < ps a (Fp L U) % B + a x := wit
  have hUL : ∀ x, U x = true → avail L x = true := by
    intro x hx
    rcases (pairP_iff u v x).mp hx with h | h
    · subst h; exact hu
    · subst h; exact hv
  have hne : ∃ x, U x = true := ⟨u, (pairP_iff u v u).mpr (Or.inl rfl)⟩
  have hpair : ps a U = a u + a v := ps_pair a huv
  by_cases hs : a u + a v ≤ B
  · exact realise_small a B apos Bpos _ L (Nat.le_refl _) run U hne hUL (by omega) wit
  apply Classical.byContradiction
  intro nost
  have noexact : ∀ E : Fin k → Bool, (∀ i, E i = true → Fp L U i = true) → ps a E ≠ B := by
    intro E hEF hEB
    have run' := run_exact a B run E (fun i h => Fp_avail (hEF i h)) hEB
    have cl := ps_avail_close a L E (fun i h => Fp_avail (hEF i h))
    obtain ⟨hav, wit'⟩ := witness_after_block a B U E hEF hEB wit
    have hu' := hav u ((pairP_iff u v u).mpr (Or.inl rfl)) hu
    have hv' := hav v ((pairP_iff u v v).mpr (Or.inr rfl)) hv
    exact nost (ih _ (by omega) _ (Nat.le_refl _) run' u v huv hu' hv' wit')
  have Fbig := fbig a B run U hne hUL wit nost
  have split := ps_avail_split a L U hUL
  have big : B ≤ ps a (avail L) := by omega
  -- B1: a maximal subset G of the fired part, topped up by one bundle x of U, is exact
  obtain ⟨G, -, hGF, hGB, hGmax⟩ :=
    exists_maximal a B apos (Fp L U) _ (fun _ => false) (Nat.le_refl _) (fun i h => by simp at h)
      (by rw [ps_zero a _ (fun _ => rfl)]; exact Nat.zero_le _)
  obtain ⟨x, hxU, hGx⟩ := room a B apos run nost big U noexact G hGF hGB
  have hother : ∃ y, y ≠ x ∧ ∀ i, U i = true ↔ (i = x ∨ i = y) := by
    rcases (pairP_iff u v x).mp hxU with h | h
    · subst h; exact ⟨v, fun e => huv e.symm, fun i => pairP_iff x v i⟩
    · subst h
      exact ⟨u, huv, fun i => by rw [pairP_iff]; exact ⟨fun h => h.symm, fun h => h.symm⟩⟩
  obtain ⟨y, hyx, hU⟩ := hother
  have hyU : U y = true := (hU y).mpr (Or.inr rfl)
  have hxy : a x + a y = a u + a v := by
    rcases (pairP_iff u v x).mp hxU with h | h
    · subst h
      have : y = v := by
        rcases (pairP_iff x v y).mp hyU with h | h
        · exact absurd h hyx
        · exact h
      subst this; rfl
    · subst h
      have : y = u := by
        rcases (pairP_iff u x y).mp hyU with h | h
        · exact h
        · exact absurd h hyx
      subst this; omega
  have hGxf : G x = false := by
    cases hg : G x
    · rfl
    · have := Fp_notU (hGF x hg); rw [hxU] at this; cases this
  let C1 : Fin k → Bool := fun i => G i || decide (i = x)
  have psC1 : ps a C1 = ps a G + a x := ps_insert a G x hGxf
  have hC1L : ∀ i, C1 i = true → avail L i = true := by
    intro i h
    simp only [C1, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact Fp_avail (hGF i h)
    · subst h; exact hUL _ hxU
  have hC1eq : ps a C1 = B := by
    apply maxExact a B run nost big C1 hC1L _ (by omega)
    intro i hav hc
    simp only [C1, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    by_cases hUi : U i = true
    · rcases (hU i).mp hUi with h | h
      · exact absurd h hc.2
      · subst h; omega
    · have hFi : Fp L U i = true := by simp [Fp, hav]; simpa using hUi
      have := hGmax i hFi hc.1
      omega
  have run1 := run_exact a B run C1 hC1L hC1eq
  have cl1 := ps_avail_close a L C1 hC1L
  have av1 : ∀ i, avail (L ++ lst C1) i = (avail L i && !C1 i) := avail_append L C1
  -- B2: a maximal subset G' of the rest of the fired part, topped up by y, is exact
  let P1 : Fin k → Bool := fun i => Fp L U i && !G i
  obtain ⟨G', -, hG'P, hG'B, hG'max⟩ :=
    exists_maximal a B apos P1 _ (fun _ => false) (Nat.le_refl _) (fun i h => by simp at h)
      (by rw [ps_zero a _ (fun _ => rfl)]; exact Nat.zero_le _)
  have hG'F : ∀ i, G' i = true → Fp L U i = true := by
    intro i h; have := hG'P i h; simp only [P1, Bool.and_eq_true] at this; exact this.1
  have hG'lt : ps a G' < B := by have := noexact G' hG'F; omega
  have hG'y : G' y = false := by
    cases hg : G' y
    · rfl
    · have := Fp_notU (hG'F y hg); rw [hyU] at this; cases this
  have hG'L1 : ∀ i, G' i = true → avail (L ++ lst C1) i = true := by
    intro i h
    rw [av1]
    have hP := hG'P i h
    simp only [P1, Bool.and_eq_true, Bool.not_eq_true'] at hP
    have hix : i ≠ x := by
      intro e; subst e; have := Fp_notU hP.1; rw [hxU] at this; cases this
    simp [Fp_avail hP.1, C1, hP.2, hix]
  have rest1 : ∀ i, avail (L ++ lst C1) i = true → i = y ∨ P1 i = true := by
    intro i h
    rw [av1] at h
    simp only [C1, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
      decide_eq_false_iff_not] at h
    by_cases hUi : U i = true
    · rcases (hU i).mp hUi with e | e
      · exact absurd e h.2.2
      · exact Or.inl e
    · right; simp [P1, Fp, h.1, h.2.1]; simpa using hUi
  have hyL1 : avail (L ++ lst C1) y = true := by
    rw [av1]
    have hGy : G y = false := by
      cases hg : G y
      · rfl
      · have := Fp_notU (hGF y hg); rw [hyU] at this; cases this
    simp [hUL y hyU, C1, hGy, hyx]
  have fitY : ps a G' + a y ≤ B := by
    apply Classical.byContradiction
    intro hno
    apply nost
    apply stuck_of_maximal a B run1 G' hG'L1 hG'lt
    · intro i hav hg
      rcases rest1 i hav with e | e
      · subst e; omega
      · exact hG'max i e hg
    · exact ⟨y, hyL1, hG'y⟩
  let C2 : Fin k → Bool := fun i => G' i || decide (i = y)
  have psC2 : ps a C2 = ps a G' + a y := ps_insert a G' y hG'y
  have hC2L : ∀ i, C2 i = true → avail (L ++ lst C1) i = true := by
    intro i h
    simp only [C2, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with h | h
    · exact hG'L1 i h
    · subst h; exact hyL1
  have big1 : B ≤ ps a (avail (L ++ lst C1)) := by omega
  have hC2eq : ps a C2 = B := by
    apply maxExact a B run1 nost big1 C2 hC2L _ (by omega)
    intro i hav hc
    simp only [C2, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hc
    rcases rest1 i hav with e | e
    · exact absurd e hc.2
    · have := hG'max i e hc.1; omega
  have run2 := run_exact a B run1 C2 hC2L hC2eq
  have cl2 := ps_avail_close a (L ++ lst C1) C2 hC2L
  -- B4: what is left lies in the fired part
  have rest2 : ∀ i, avail (L ++ lst C1 ++ lst C2) i = true → Fp L U i = true := by
    intro i h
    rw [avail_append] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    rcases rest1 i h.1 with e | e
    · subst e; simp [C2] at h
    · simp only [P1, Bool.and_eq_true] at e; exact e.1
  have restlt := small_rest a B apos run2 nost (fun E' hE' => noexact E' (fun i h => rest2 i (hE' i h)))
  obtain ⟨z, hzU, hRz⟩ := room a B apos run nost big U noexact _ rest2 (by omega)
  -- B5: count
  have w := wit z hzU
  have := apos z
  have FB : ps a (Fp L U) < B + B := by omega
  have hmod := mod_of_two B (ps a (Fp L U)) Bpos Fbig FB
  omega

/-! ## Consequences for the star -/

theorem avail_nil (i : Fin k) : avail ([] : List (Fin k)) i = true := by simp [avail]

/-- **Corollary.** If some set `U` of senders, of total at most `B` or of size two,
overflows on top of the residue of the other senders' total, then a bad
capacity-terminal state is reachable from the start. -/
theorem bad_of_small_or_pair_witness (apos : ∀ i, 0 < a i) (Bpos : 0 < B)
    (U : Fin k → Bool) (hne : ∃ u, U u = true)
    (shape : ps a U ≤ B ∨ ∃ u v, u ≠ v ∧ ∀ i, U i = pairP u v i)
    (wit : ∀ u, U u = true → B < ps a (fun i => !U i) % B + a u) :
    ∃ y, Reaches (Step a B) (stateOf a [] 0) y ∧
        CapacityTerminal (mult a) (out a B) (cap a B) y ∧ ¬ OrdinaryStable (out a B) y := by
  apply (bad_terminal_reachable_iff a B apos).mpr
  have hF : ∀ V : Fin k → Bool, ps a (Fp [] V) = ps a (fun i => !V i) := fun V =>
    ps_congr a (fun i => by simp [Fp, avail_nil])
  have st : Stuck a B := by
    rcases shape with h | ⟨u, v, huv, hUeq⟩
    · exact realise_small a B apos Bpos _ [] (Nat.le_refl _) Run.nil U hne
        (fun i _ => avail_nil i) h (fun u hu => by rw [hF]; exact wit u hu)
    · have hUe : U = pairP u v := funext hUeq
      subst hUe
      exact realise_pair a B apos Bpos _ [] (Nat.le_refl _) Run.nil u v huv (avail_nil u)
        (avail_nil v) (fun x hx => by rw [hF]; exact wit x hx)
  exact st

end Star

end CBMDFixedState
