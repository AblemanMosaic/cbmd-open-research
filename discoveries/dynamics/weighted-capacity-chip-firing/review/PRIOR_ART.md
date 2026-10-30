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

## The statement to compare against

For an ordered multigraph with absorbing sink, if every vertex satisfies
`C(v) >= d(v) + max_u m(u,v) - 1`, then every capacity-blocked terminal state
equals the ordinary normal form; and the bound is sharp at every receiver of
incoming multiplicity at least two.

A prior-art match must carry an explicit translation of capacity, firing
threshold, transfer multiplicity, and terminal-state semantics. The most likely
places for an equivalent are the bounded-Petri-net deadlock literature and work
on capacity-constrained abelian networks.
