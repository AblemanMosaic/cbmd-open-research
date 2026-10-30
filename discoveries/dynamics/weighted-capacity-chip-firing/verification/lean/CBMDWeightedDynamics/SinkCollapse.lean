/-!
# A capacitated sink collapses the theory

Every result in this dossier assumes an **absorbing** sink: chips sent there
leave the system and are never capped.  This module settles what happens when
the sink instead holds chips under a finite capacity — the case the dossier
listed as out of scope.

The answer is total collapse.  With a capacitated sink, every firing strictly
increases some capacitated coordinate: a neighbour, or the sink itself.  So
the all-full state — every vertex at capacity, the sink at its cap — is
capacity-terminal, and if any vertex is live it is not ordinarily stable.
Transfer then fails at **every** finite sink capacity.  Conversely, if no
vertex is live, nothing can ever be unstable and transfer holds trivially.

The absorbing sink is therefore not a convenience: it is the limit of the sink
capacity, and no finite stage of that limit supports the theory.  This is the
chip-firing face of the all-full obstruction of
`CBMD-CON-CAPACITY-PRESERVATION-001`, stated here in this dossier's own terms.

No declaration uses `sorry` or introduces an axiom.
-/

namespace CBMDWeightedDynamics

namespace CappedSink

variable {n : Nat}

/-- A chip-firing system on `n` nonsink vertices whose sink is capacitated.
`toSink v` is the number of chips `v` sends to the sink. -/
structure System (n : Nat) where
  mult : Fin n → Fin n → Nat
  toSink : Fin n → Nat
  outdegree : Fin n → Nat
  capacity : Fin n → Nat
  sinkCap : Nat

/-- A state: chips on the nonsink vertices and in the sink. -/
structure State (n : Nat) where
  chips : Fin n → Nat
  sink : Nat

def Unstable (S : System n) (x : State n) (v : Fin n) : Prop :=
  S.outdegree v ≤ x.chips v

def OrdinaryStable (S : System n) (x : State n) : Prop :=
  ∀ v, ¬ Unstable S x v

/-- Capacity-legal firing: unstable, and every receiver — the sink included —
stays within capacity. -/
def Legal (S : System n) (x : State n) (v : Fin n) : Prop :=
  Unstable S x v ∧ (∀ w, x.chips w + S.mult v w ≤ S.capacity w) ∧
    x.sink + S.toSink v ≤ S.sinkCap

def CapacityTerminal (S : System n) (x : State n) : Prop :=
  ∀ v, ¬ Legal S x v

def Admissible (S : System n) (x : State n) : Prop :=
  (∀ v, x.chips v ≤ S.capacity v) ∧ x.sink ≤ S.sinkCap

def Live (S : System n) (v : Fin n) : Prop := S.outdegree v ≤ S.capacity v

/-- Every vertex sends at least one chip somewhere capacitated. -/
def Sends (S : System n) : Prop :=
  ∀ v, (∃ w, 0 < S.mult v w) ∨ 0 < S.toSink v

/-- The all-full state. -/
def allFull (S : System n) : State n := ⟨S.capacity, S.sinkCap⟩

theorem allFull_admissible (S : System n) : Admissible S (allFull S) :=
  ⟨fun _ => Nat.le_refl _, Nat.le_refl _⟩

/-- **The all-full state is capacity-terminal** once every vertex sends a chip
somewhere capacitated. -/
theorem allFull_terminal {S : System n} (sends : Sends S) :
    CapacityTerminal S (allFull S) := by
  intro v ⟨_, fits, sinkFits⟩
  rcases sends v with ⟨w, hw⟩ | hs
  · have := fits w
    simp only [allFull] at this
    omega
  · simp only [allFull] at sinkFits
    omega

/-- **Collapse.**  With a capacitated sink, if some vertex is live then the
all-full state is an admissible capacity-terminal state that is not ordinarily
stable — so it is not the ordinary normal form of anything, and transfer
fails.  The witness uses only the capacities, so no finite sink capacity, and
no enlargement of the vertex capacities, avoids it. -/
theorem capped_sink_breaks_transfer {S : System n} (sends : Sends S)
    {v : Fin n} (live : Live S v) :
    Admissible S (allFull S) ∧ CapacityTerminal S (allFull S) ∧
      ¬ OrdinaryStable S (allFull S) :=
  ⟨allFull_admissible S, allFull_terminal sends, fun stable => stable v live⟩

/-- The converse: if no vertex is live, every admissible state is ordinarily
stable, so it is its own ordinary normal form and its own capacity-terminal
state, and transfer holds trivially. -/
theorem no_live_all_stable {S : System n} (none : ∀ v, ¬ Live S v)
    {x : State n} (adm : Admissible S x) : OrdinaryStable S x := by
  intro v unstable
  exact none v (Nat.le_trans unstable (adm.1 v))

end CappedSink

end CBMDWeightedDynamics
