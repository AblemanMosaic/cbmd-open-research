# Written argument: DAG receiver-capacity preservation

Status: provisional theorem; exact unit-edge model and full transfer theorem
Lean-compiled; novelty review remains open.

## Theorem candidate FD-C1

Let `G` be a finite loopless directed graph with an absorbing sink `q`. Assume:

1. every nonsink edge has multiplicity one;
2. the nonsink graph is acyclic;
3. every nonsink vertex reaches `q`;
4. receiver capacity satisfies `C(v) >= d(v)` for every nonsink vertex, where
   `d(v)` is its total outdegree including sink edges.

Then capacity-blocked chip-firing terminates and, from every admissible initial
state, reaches the same normal form as ordinary chip-firing.

## Proof

Fix a topological ordering of the nonsink vertices. First, every
capacity-blocked firing is an ordinary legal firing: it satisfies the ordinary
threshold condition and performs exactly the ordinary chip transfer.

Every ordinary firing sequence terminates. Read the chip vector
lexicographically in topological order, with earlier vertices more significant.
A firing strictly decreases its source coordinate, and it can change only
strictly later coordinates. Hence every firing strictly decreases a
well-founded lexicographic order. Capacity firings form a subrelation, so they
terminate as well.

It remains to show that a terminal capacity-blocked state is ordinarily stable.
Suppose instead that a terminal state `x` contains at least one ordinarily
unstable vertex. Choose a topologically latest such vertex `u`. Because `u`
cannot fire under the capacity rule, some unit edge `u -> v` must be blocked:

`x(v) + 1 > C(v)`.

For natural numbers this implies `C(v) <= x(v)`. By assumption
`C(v) >= d(v)`, so `v` is ordinarily unstable. (Admissibility additionally
forces `x(v) = C(v)`, but that equality is not needed.) But `v` is strictly later than
`u` in the topological order, contradicting the choice of `u`. Therefore every
capacity terminal state is ordinarily stable.

Ordinary chip-firing on this ordered unit-edge graph has a unique
stabilization. If two distinct vertices are legal, firing either one cannot
make the other illegal: it either leaves the other's chip count unchanged or
adds one. The two firings commute. At a source coordinate this uses the
original legality inequality to justify commuting natural subtraction with a
possible incoming increment. Thus one-step forks are joinable. Termination and
the terminal form of Newman's lemma give a unique reachable stable state.

Since a capacity-blocked execution is an ordinary legal execution and
terminates at an ordinary stable state, its final state must be that unique
ordinary stabilization. This proves the claim.

## Why each boundary matters

- With a directed cycle, the “topologically latest unstable vertex” need not
  exist. The recorded three-vertex witness has two distinct terminal states.
- With a parallel edge of multiplicity two, overflow does not imply that the
  receiver is full. The recorded two-vertex DAG can be terminal under the
  capacity rule while its source remains ordinarily unstable.
- If `C(v) < d(v)`, a full receiver need not itself be ordinarily unstable.
- Without sink reachability, ordinary stabilization need not terminate.

## Nonclaims

- No novelty or priority is claimed.
- The theorem does not cover cyclic graphs, parallel edges, partial transfers,
  stochastic rules, infinite graphs, or capacities below outdegree.
- The finite enumeration is corroboration and fault detection, not the proof.
- The theorem does not certify that an external graph file was correctly
  decoded into the Lean edge and outdegree parameters.

