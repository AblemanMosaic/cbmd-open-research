# Where the live-set characterization transfers, and where it stops

## The question

`CBMD-DYN-WEIGHTED-CAPACITY-001` characterizes when a capacity constraint
preserves the terminal states of chip-firing. Its proof uses very little about
chip-firing: only that firing adds to other vertices, that a blocked sender
implies a full receiver, and that a full receiver is above *its own* firing
threshold. The natural question is how much of that is load-bearing.

Petri nets with place capacities are the right test. A transition may consume
from several places and several transitions may consume from one place, so the
third step above is no longer automatic. The question also sheds the confluence
assumption entirely:

> **PRESERVES(N, C)** — every capacity-reachable marking that is capacity-dead
> is also dead in the uncapacitated net.

A capacity-dead but ordinarily enabled marking is a deadlock the capacity
invented. In the chip-firing case this is exactly
`capacity_terminal_implies_ordinary_stable`.

## Chip-firing shape, in net terms

A net is **chip-firing shaped** when every transition consumes from exactly one
place, distinct transitions consume from distinct places, and no transition
produces back into the place it consumes.

Translating the live-set conditions into this setting — `Live q` iff the
capacity of `q` admits the threshold of the transition draining it; the bound on
arcs between live places; closure of live under those arcs; acyclicity — the
characterization is **exact**:

| box | systems | both | unsound | incomplete |
|---|---|---|---|---|
| 2 places, 2 transitions, weights ≤ 2, capacities ≤ 3 | 1,152 | 552 | **0** | **0** |
| 3 places, 3 transitions, weights ≤ 1, capacities ≤ 2 | 10,368 | 3,024 | **0** | **0** |

This is an independent reproduction of the chip-firing characterization in a
differently coded model: markings and transitions rather than chips and
vertices, with a separately written enabledness and reachability routine.

## Which structural feature is load-bearing

Relaxing one feature at a time, counting only the newly admitted nets:

| relaxation | unsound | incomplete | verdict |
|---|---|---|---|
| none (control) | 0 | 0 | exact |
| transition may feed its own input place | **0** | 1,636 | still **sound**, now incomplete |
| two transitions may drain one place | 80 | 112 | **unsound** |
| a transition may have several input places | 48 | 514 | **unsound** |

Self-feedback is the surprise: it costs completeness but not soundness. The
conditions remain sufficient for nets where a transition returns tokens to the
place it drains, over the whole newly admitted class. The two features that
actually break sufficiency are shared consumption and conjunctive input — and
those are precisely the two things chip-firing does not have.

### Minimal witnesses

**Shared consumption.** `pre = [[0,1],[1,2]]` restricted to one place, with
`t0` draining place 1 and `t1` draining place 1 at threshold 2, capacity `(0,1)`.
Marking `(0,1)` is capacity-dead while `t0` is ordinarily enabled. The conditions
pass because the liveness test consulted the wrong consumer.

**Conjunctive input.** `pre = [[0,1],[1,2]]`, `post = [[1,0],[0,0]]`, capacity
`(1,2)`. At marking `(1,1)`, `t0` is ordinarily enabled but blocked, because
firing it would push place 0 to 2 over a capacity of 1. The descent then needs
place 0's consumer `t1` to be enabled; place 0 *is* above `t1`'s threshold
there, but `t1` also needs two tokens from place 1 and only one is present.

## A generalization that still fails

The two failures above both look like the liveness notion being too crude, so
the obvious repair is to track which transitions can fire at all:

- `t` is **usable** when every input threshold of `t` fits inside the capacities;
- `Live q` when some usable transition consumes from `q`;
- the bound and closure quantify over usable transitions and their consumers.

This repair is **not** enough. Over three boxes the refined conditions are still
unsound:

| box | unsound | incomplete |
|---|---|---|
| 2 places, 2 transitions, weights ≤ 2, capacities ≤ 3 | 64 | 18,466 |
| 3 places, 3 transitions, weights ≤ 1, capacities ≤ 2 | 7,200 | 1,254,024 |
| 2 places, 3 transitions, weights ≤ 2, capacities ≤ 2 | 552 | 655,087 |

The mechanism is visible in the conjunctive-input witness. The descent argument
certifies one place at a time: *this* receiver is full, therefore *this* receiver
is above a threshold, therefore something downstream can fire. Enabledness of a
multi-input transition is a conjunction over places, and no amount of
per-place capacity bookkeeping discharges a conjunction.

We do **not** claim that no local capacity condition can repair the multi-input
case; only that this natural one does not, with explicit witnesses.

## Standing

Finite censuses over the stated boxes. The chip-firing characterization itself
is proved and compiled in `CBMD-DYN-WEIGHTED-CAPACITY-001`; this dossier maps
where it transfers and gives witnesses where it does not. No unbounded theorem
about general Petri nets is established, and novelty is unassessed.

## The increasing class, proved

Everything above is census. This section is a theorem, compiled in
[`../verification/lean/`](../verification/lean/).

Call a net **increasing** when every transition strictly increases the token
count at some place:

```
for every t there is a q with  post(t, q) > pre(t, q)
```

and **inert** at a capacity vector `C` when no transition can ever fire inside
the box:

```
for every t there is a q with  C(q) < pre(t, q)
```

> **Theorem (all-full obstruction).** For an increasing net,
> `PRESERVES(N, C)` holds if and only if `N` is inert at `C`.

*Proof.* Suppose `N` is inert. At any admissible `m` and any `t`, pick `q` with
`C(q) < pre(t,q)`; then `m(q) ≤ C(q) < pre(t,q)`, so `t` is not ordinarily
enabled. No admissible marking enables anything, so preservation holds.

Suppose `N` is not inert, so some `t₀` has `pre(t₀,q) ≤ C(q)` at every `q`.
Take the marking `m = C`, which is admissible. For any `t`, pick `q` with
`post(t,q) > pre(t,q)`. Either `t` is not ordinarily enabled at `C`, and then
not capacity enabled; or it is, and then `pre(t,q) ≤ C(q)`, so firing would
leave `C(q) − pre(t,q) + post(t,q) > C(q)`, which the capacity refuses. Either
way `t` is not capacity enabled, so `C` is capacity-dead. But `t₀` is ordinarily
enabled at `C`. Preservation fails. ∎

Three remarks.

**No capacity escapes it.** The witness is the capacity vector itself, so
raising capacities reruns the same argument at the new all-full marking. This is
the shape of the filled-set obstruction in the predecessor dossier, with the
filled set taken to be every place.

**It explains the sink.** A chip-firing vertex's transition adds chips to its
out-neighbours, so it increases a place — unless the receiver is the absorbing
sink, which carries no capacity and is therefore not a place of this model at
all. The sink is precisely what keeps chip-firing out of the hypothesis. Read in
reverse, the theorem says a capacitated chip-firing model without a sink cannot
work, whatever capacities are chosen.

**The hypothesis is not decoration.** Outside the increasing class the
conclusion is simply false: a net whose transitions only drain can fire happily
and still invent no deadlock. In the measured boxes the conclusion would be
wrong on 39,464 such nets.

The modelling step is proved too. The census quantifies over markings
capacity-reachable from an admissible initial marking; the theorem quantifies
over admissible markings. `preserves_iff_reachable_form` shows these agree,
because capacity firing cannot leave the box and every admissible marking is
reachable from itself.

## The draining regime: the flow characterization

The all-full obstruction stops at draining transitions. For unit-weight flow
nets — each transition takes one token from `src` and either delivers it to
`dst` or discards it — the full answer is a filled-set condition.

A set `S` of places is an **obstruction** at capacity `C` when

1. `C(q) ≥ 1` for every `q ∈ S`;
2. no drain has its source in `S`;
3. every mover `u → w` with `u ∈ S` has `w ∈ S` or `C(w) = 0`;
4. some mover has its source in `S`.

> **Theorem.** `PRESERVES(N, C)` if and only if no obstruction exists.

*Obstruction ⇒ failure.* Put `m(q) = C(q)` for `q ∈ S` and `m(q) = 0`
otherwise; `m` is admissible. A transition with source outside `S` is not
ordinarily enabled. A transition with source in `S` is a mover, by 2, with some
destination `w`; by 3 either `w ∈ S`, so `m(w) = C(w)` and one more token
overflows, or `C(w) = 0`, so `m(w) = 0` and one more token still overflows.
Hence `m` is capacity-dead. By 4 and 1 some mover's source holds a token, so
`m` is ordinarily enabled. Preservation fails.

*Failure ⇒ obstruction.* Let `m` be admissible, capacity-dead and ordinarily
enabling some `t₀`. Put `S = {q : m(q) ≥ 1}`. Then 1 is admissibility; 2 holds
because a drain from `S` would be capacity-enabled; for 3, capacity-deadness of
a mover from `S` to `w` forces `C(w) < m(w) + 1`, so `m(w) = C(w)`, and then
either `C(w) = 0` or `w ∈ S`; and `t₀` cannot be a drain, so 4 holds. ∎

Two remarks.

**Zero capacity blocks as well as fullness does.** Clause 3's second branch is
the only place the two differ, and it is what makes the statement an
equivalence rather than merely sufficient.

**Clause 4 is not bookkeeping.** Without it the condition is sound but
incomplete: a set of full places that no transition draws from blocks nothing.
The smallest witness is three movers `0 → 1` with capacities `(0, 0, 1)`, where
`{2}` satisfies 1–3 and the net nonetheless preserves.

Specializing: with no drains and all capacities positive, this is the live-set
obstruction of `CBMD-DYN-WEIGHTED-CAPACITY-001`; taking `S` to be every place
recovers the all-full obstruction of the previous section.

## Where the boundary becomes a complexity boundary

The previous two sections are theorems about nets whose transitions have one
input place. The census of version 0.1.0 found that the characterization breaks
at two. The two facts are the same fact.

**Membership.** `PRESERVES(N, C)` asserts that no admissible marking is both
capacity-dead and ordinarily enabled. The complement is in NP: an admissible
marking is bounded by `C`, so it has polynomial size even with capacities
written in binary, and both halves of "bad" are checked in `O(PT)` arithmetic
operations. Hence preservation is in coNP.

**Hardness.** A transition fails to be capacity enabled in exactly two ways:

```
(A)  some q has  m(q) < pre(t,q)
(B)  some q has  m(q) - pre(t,q) + post(t,q) > C(q)
```

Take unit weights and capacities in `{0,1}`. Then (A) with `pre(t,q) = 1` says
`q` is false — a negative literal, and an input place — while (B) with
`pre(t,q) = 0`, `post(t,q) = 1`, `C(q) = 1` says `q` is true — a positive
literal, and no input place. One transition per clause, consuming from the
places of its negative literals and producing into the places of its positive
ones, is therefore blocked precisely when its clause is satisfied, and it has
as many input places as the clause has negative literals.

The other half of a bad marking, that something is ordinarily enabled, is
supplied by one transition per atom place: it consumes from that place and
produces into a place of capacity zero, so it is blocked always and ordinarily
enabled exactly when the atom holds a token.

Requiring every transition to have an input place — this dossier's census
generator excludes input-free transitions, so the reduction should not need
them — forces every clause to carry a negative literal, and such a CNF is
always satisfied by the all-false assignment. The reduction therefore targets

> given a CNF in which every clause has at least one negative literal, is there
> a model that is not all-false?

which is what the construction asks. Given an arbitrary CNF over `x₁..xₙ`,
introduce complements `x̄ᵢ` and a guard `g`:

```
(¬xᵢ ∨ ¬x̄ᵢ)                      (¬xᵢ ∨ g)        (¬x̄ᵢ ∨ g)
(xᵢ ∨ x̄ᵢ ∨ ¬g)                   each original clause with ¬xᵢ as x̄ᵢ, then ∨ ¬g
```

A model that is not all-false must make `g` true, since otherwise the guard
clauses force every atom false. With `g` true the first two families make each
pair one-hot, giving a total assignment, and the rewritten clauses say it
satisfies the original formula; the converse is immediate. No clause has more
than two negative literals and none has fewer than one, so every transition has
one or two input places.

So deciding preservation is coNP-complete already at two input places, unit
weights and `{0,1}` capacities — and polynomial at one, by the fixpoint of the
preceding section. No polynomial-time condition, local or otherwise, is exact
for multi-input transitions unless `P = NP`.

This is a written argument. Unlike the two preceding sections it is not
compiled; what is machine-checked is the correctness of the reduction.
