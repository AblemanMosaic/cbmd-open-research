# Bounded prior-art note

Date 2026-10-30. Outcome: **no match located; novelty remains UNASSESSED.**
A failed search is not a novelty result. These queries are recorded so a
successor starts here rather than repeating them.

## Classical context that is NOT claimed

- Ordinary chip-firing termination, the abelian property, and uniqueness of the
  stabilization. Entirely classical and used here only as explicit hypotheses.
- Newman's lemma and local-confluence arguments.
- Finite-capacity (bounded-place) Petri-net semantics: the receiver-storage
  legality condition is exactly that, and is not claimed.
- The notion of an implicit or redundant place, i.e. a capacity that never
  restricts firing. The present condition is weaker: the capacity here *does*
  block firings transiently; what is preserved is only the set of terminal
  states.

## Queries run

| Query | Outcome |
|---|---|
| chip-firing with vertex capacity bounded sandpile confluence capacity-constrained abelian | survey and sandpile literature; no capacity-threshold preservation theorem located |
| finite capacity Petri net confluence bounded place capacity same final marking acyclic | general P/T-net theory and a confluence-property paper; no multiplicity-indexed capacity threshold located |
| "implicit place" Petri net capacity constraint does not change reachable dead markings redundant | structural-redundancy literature; the implicit-place notion is strictly stronger than what is used here |
| chip-firing game bounded vertex capacity stabilization unchanged threshold outdegree plus maximum edge multiplicity | chip-firing surveys and theses; no match |

## Queries run for the characterization (revision 0.3.0 / 0.4.0)

| Query | Outcome |
|---|---|
| bounded Petri net capacity constraint preserves dead markings deadlock-free acyclic live places characterization | general bounded-net theory, non-blockingness verification and deadlock analysis; no live-set characterization of capacity-preserving nets located |
| blocking tandem queueing network deadlock if and only if cycle finite buffer manufacturing blocking-after-service | large literature on blocking in tandem and cyclic queues, concerned with throughput and mean cycle time rather than with preservation of terminal configurations |

**A partial prior-art acknowledgement.** The cycle obstruction has a direct
reading in queueing and manufacturing: a finite-buffer network with
blocking-after-service deadlocks when a cycle of stations is simultaneously
full, and feed-forward lines do not deadlock. That a cycle is what makes
blocking deadlock is **folklore in that field** and is not claimed as new here.
What the located literature studies is performance — throughput, mean cycle
time, approximations — not the structural question of whether the blocked system
reaches the same terminal configuration as the unblocked one, and not a
condition on capacities indexed by transfer multiplicity. Those are the parts
still unmatched.

The live-set condition has a natural Petri-net reading: a place whose capacity is
below the firing threshold of its own output transition can never enable that
transition, and a transition feeding such a place can deadlock while the
uncapacitated net proceeds. The nearest named notions are **implicit places**
(capacities that never restrict firing, strictly stronger than what is needed
here) and **non-blockingness** of bounded nets (a reachability property rather
than a structural condition on capacities). Neither is the statement below.

## The statement to compare against

For an ordered multigraph with absorbing sink, if every vertex satisfies
`C(v) >= d(v) + max_u m(u,v) - 1`, then every capacity-blocked terminal state
equals the ordinary normal form; and the bound is sharp at every receiver of
incoming multiplicity at least two.

Over arbitrary digraphs, with `Live v` meaning `C(v) >= d(v)`: preservation holds
exactly when the live subgraph is acyclic, satisfies the bound on its arcs, and
is closed under arcs leaving live vertices.

A prior-art match must carry an explicit translation of capacity, firing
threshold, transfer multiplicity, and terminal-state semantics. The most likely
places for an equivalent are the bounded-Petri-net deadlock literature and work
on capacity-constrained abelian networks.
