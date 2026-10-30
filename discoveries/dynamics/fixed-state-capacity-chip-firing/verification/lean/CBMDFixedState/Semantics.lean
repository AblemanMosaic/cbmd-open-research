/-!
# Capacity-blocked chip-firing semantics

These definitions are copied verbatim from `CBMD-DYN-WEIGHTED-CAPACITY-001`
(`CBMDWeightedDynamics/Core.lean`, `Transfer.lean`, `Concrete.lean`), so the
fixed-state results here are about exactly the model characterized there.  A
custody check in `verification/` compares the copied text with the original.
-/

namespace CBMDFixedState

abbrev Vertex (n : Nat) := Fin n
abbrev Chips (n : Nat) := Vertex n → Nat

def OrdinaryUnstable {n : Nat}
    (outdegree chips : Vertex n → Nat) (v : Vertex n) : Prop :=
  outdegree v ≤ chips v

def OrdinaryStable {n : Nat}
    (outdegree : Vertex n → Nat) (chips : Chips n) : Prop :=
  ∀ v, chips v < outdegree v

def ReceiverBlocked {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (capacity chips : Vertex n → Nat) (u : Vertex n) : Prop :=
  ∃ v, 0 < mult u v ∧ capacity v < chips v + mult u v

def CapacityLegal {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n) (u : Vertex n) : Prop :=
  OrdinaryUnstable outdegree chips u ∧ ¬ ReceiverBlocked mult capacity chips u

def CapacityTerminal {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (outdegree capacity : Vertex n → Nat)
    (chips : Chips n) : Prop :=
  ∀ u, ¬ CapacityLegal mult outdegree capacity chips u

def CapacityStep {n : Nat}
    (mult : Vertex n → Vertex n → Nat)
    (fire : Chips n → Vertex n → Chips n)
    (outdegree capacity : Vertex n → Nat)
    (before after : Chips n) : Prop :=
  ∃ u, CapacityLegal mult outdegree capacity before u ∧ fire before u = after

inductive Reaches {α : Sort _} (step : α → α → Prop) : α → α → Prop
  | refl (x : α) : Reaches step x x
  | tail {x y z : α} : Reaches step x y → step y z → Reaches step x z

def wFire {n : Nat} (mult : Vertex n → Vertex n → Nat) (outdegree : Vertex n → Nat)
    (chips : Chips n) (u : Vertex n) : Chips n :=
  fun v => if v = u then chips v - outdegree u else chips v + mult u v

end CBMDFixedState
