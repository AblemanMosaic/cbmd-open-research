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

## Abelian networks: the closest general framework, and why it does not apply

Added 2026-10-31. This is the one general theory that would plausibly subsume
the preservation theorem, and it was missing from the queries above.

- **B. Bond and L. Levine, *Abelian networks I. Foundations and examples*,
  arXiv:1309.3445.** Read: the definition of an abelian processor and network
  (§2) and the order-independence results (§4), via the arXiv PDF; the full
  text was also searched for "capacity", "bounded in-degree", "blocked",
  "blocking" and "room", none of which occurs.
  - Definition 2.1 (abelian processor): for any two input words with the same
    letter counts the resulting state agrees, and each output word has the same
    letter counts.
  - Lemma 4.3 (least action principle), Lemma 4.4 (halting dichotomy: either no
    finite complete execution exists, or every legal execution is finite and
    all complete legal executions have the same letter counts), and Theorem 4.6
    (halting status, final states and run times are independent of execution
    order).
  - **Why the present model is not an abelian network.** Their processors are
    local. In their words:

    > "An individual processor in an abelian network cannot access the states of
    > neighboring processors. It can only read the messages they send."

    Capacity-blocked firing is exactly the opposite: a vertex may fire only if
    its *receivers* have room, so the enabling condition reads the state of
    neighbouring vertices. Their model has no capacity on input ports and
    messages accumulate without bound, and the paper never treats a firing
    forbidden by a full receiver. So Theorem 4.6 does not apply here, and the
    preservation theorem is not a corollary of it.
  - What this does mean: the *conclusion* of the present theorem — every
    reachable capacity-terminal state is the ordinary normal form — is the
    analogue of their Lemma 4.4 and Theorem 4.6 for a rule that is not local.
    The content is in recovering an abelian-style conclusion for a non-local
    firing rule, under the capacity threshold and the acyclicity hypothesis;
    the cycle converse shows both hypotheses are needed.
  - **Not read:** *Abelian networks II. Halting on all inputs*
    (arXiv:1409.0169) and *III. The critical group*. They were located but not
    read; II concerns halting on all inputs and III the critical group, neither
    of which is the question here, but this is recorded as a gap rather than
    as a clearance.
- **A. E. Holroyd, L. Levine and P. Winkler, *Abelian logic gates*.** Located
  in the same search, not read. Noted because abelian logic gates are the
  natural place a "blocking" gate might appear.

This changes the standing of the bounded note above: the closest general
theory is now identified by name, with the definitional reason it does not
cover the model quoted from the source. Novelty remains **UNASSESSED** — this
rules out one framework, it does not survey the field.

## Queries run for the characterization (revision 0.3.0 / 0.4.0)

| Query | Outcome |
|---|---|
| bounded Petri net capacity constraint preserves dead markings deadlock-free acyclic live places characterization | general bounded-net theory, non-blockingness verification and deadlock analysis; no live-set characterization of capacity-preserving nets located |
| blocking tandem queueing network deadlock if and only if cycle finite buffer manufacturing blocking-after-service | large literature on blocking in tandem and cyclic queues, concerned with throughput and mean cycle time rather than with preservation of terminal configurations |

**A prior-art acknowledgement, sharpened.** The cycle obstruction has a direct
reading in queueing and manufacturing: a finite-buffer network with
blocking-after-service deadlocks when a cycle of stations is simultaneously
full, and feed-forward lines do not deadlock. That a cycle is what makes
blocking deadlock is **folklore in that field** and is not claimed as new here.

A later search, run for the companion dossier
[`CBMD-CON-CAPACITY-PRESERVATION-001`](../../../concurrency/capacity-preservation-boundary/review/PRIOR_ART.md),
found that the folklore is in fact a theorem:

> Jörg Liebeherr and Ian F. Akyildiz, *Deadlock Properties of Queueing Networks
> with Finite Capacities and Multiple Routing Chains*,
> <https://www.comm.utoronto.ca/~jorg/archive/papers/CS-93-65.pdf>

Their Theorem 1 is a **necessary and sufficient** deadlock-freedom condition
for a closed network under blocking-after-service, stated over buffer cycles
and carrying the chain's job count `K_r`. So the cycle obstruction of revision
0.2.0 should be read as the Petri-net-side form of a known result, not as new.

What the located literature still does not address: the structural question of
whether the blocked system reaches the same terminal configuration as the
unblocked one; a condition on capacities indexed by transfer multiplicity; and
the weighted bound itself. Those are the parts still unmatched. Note also that
their condition carries a conserved job count, which has no analogue here
because the absorbing sink destroys chips.

**Vocabulary.** Two standard names apply and are now used in the companion
dossier: *capacity-enabled* and *ordinarily enabled* are Murata's **strict**
and **weak** transition rules, and the live-set obstruction is a **trap** in
the net (dually a siphon in the complemented net). Both are classical objects;
no novelty is claimed for the shape of the condition.

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

## Added 2026-10-30: the nearest unchecked work

A further search found a paper devoted exactly to the semantics of capacities:

> Raymond Devillers, *The Semantics of Capacities in P/T Nets*, Advances in
> Petri Nets 1989, LNCS 424, Springer 1990, pp. 128–150.
> <https://www2.informatik.uni-hamburg.de/TGI/pnbib/d/devillers_r15.html>

The catalogue abstract describes a comparison of candidate firing rules for
nets with capacities, from several viewpoints (external, internal,
place-complementation, concurrency, process semantics, expressive power). It
concludes that the behaviours can differ considerably while the main rules have
essentially the same expressive power. It does not mention terminal states,
dead markings or a condition under which two rules agree. **The full text was not
obtained.** It is the most likely place for a statement close to this dossier's,
and should be read before any novelty claim. Queries that found nothing new:
abelian networks with finite capacity (Bond–Levine halting theory, which has no
capacity blocking); sandpile models with maximum site capacity.
