# Weighted-transfer capacity-blocked chip-firing

## 1. The question

The finite-capacity chip-firing dossier (`CBMD-DYN-CAPACITY-FIRING-001`) proves
preservation for **unit** nonsink transfers under `C(v) >= d(v)`, and records as
unresolved the weighted successor with leading candidate

```
C(v) >= d(v) + max_u m(u,v) - 1.
```

This dossier resolves that candidate affirmatively, with a compiled theorem.

## 2. Exact model

Nonsink vertices `V = {0,...,n-1}`, absorbing sink `q`. Nonsink multiplicities
`m(u,v)` for `u,v in V`, sink multiplicities `m(u,q)`, and

```
d(u) = m(u,q) + sum_v m(u,v).
```

Arcs of positive multiplicity point strictly forward (`m(u,v) > 0 => u < v`).
A capacity vector `C` bounds the state box. Vertex `u` is **capacity-legal** at `x` when

1. `x(u) >= d(u)`; and
2. `x(v) + m(u,v) <= C(v)` for every nonsink `v`.

Firing removes `d(u)` chips from `u` and adds `m(u,v)` to each nonsink `v`.
**Ordinary** firing drops condition 2.

## 3. The capacity hypothesis, stated without truncation

Let `b(v)` be any upper bound on incoming multiplicity, `m(u,v) <= b(v)` for all `u`.
The hypothesis is

```
d(v) + b(v) <= C(v) + 1                                   (CapacityAdmits)
```

which is `C(v) >= d(v) + b(v) - 1` written so that no natural subtraction occurs.
Taking `b(v) = max_u m(u,v)` gives the named candidate. Taking `b(v) = 1` gives
`C(v) >= d(v)`, the unit-edge hypothesis of the predecessor theorem
(`unit_case_capacity_admits`).

Two points deserve emphasis. First, `b` need not be the maximum: any valid upper
bound works, which makes the theorem usable with a coarse global bound. Second,
the hypothesis is only ever consulted at a vertex that is some firing vertex's
receiver, so a vertex with no incoming arc is unconstrained.

## 4. The obstruction lemma

> **Lemma (weighted overflow forces instability).** If `m(u,v) <= b(v)`,
> `d(v) + b(v) <= C(v) + 1`, and `C(v) < x(v) + m(u,v)`, then `d(v) <= x(v)`.

*Proof.* `C(v) + 1 <= x(v) + m(u,v)` by the overflow hypothesis. Chaining,
`d(v) + b(v) <= C(v) + 1 <= x(v) + m(u,v) <= x(v) + b(v)`, and cancelling `b(v)`
gives `d(v) <= x(v)`. ∎

This is the exact point at which the extra `b(v) - 1` of capacity is spent: the
bundle `m(u,v)` that caused the overflow is itself at most `b(v)`, so the
overflow must have been caused by `x(v)` already standing at or above `d(v)`.
With unit transfers the lemma degenerates to `C(v) <= x(v)` and `d(v) <= C(v)`.

## 5. Preservation of terminal states

> **Theorem.** Under the hypotheses of §3 with forward-ordered arcs, every
> capacity-terminal state is ordinarily stable.

*Proof.* Induct on reverse topological position `n - u`. Suppose `u` is
ordinarily unstable at a capacity-terminal `x`. Since `x` is terminal, `u` must
be receiver-blocked: some `v` with `m(u,v) > 0` has `C(v) < x(v) + m(u,v)`. The
lemma makes `v` ordinarily unstable. Forward ordering gives `u < v`, so `v` has
strictly smaller reverse rank, and the induction hypothesis makes `v` ordinarily
stable — a contradiction. ∎

## 6. The transfer theorem

Ordinary firing theory enters only as two hypotheses, exactly as in the
predecessor: well-foundedness of the ordinary step relation, and uniqueness of
the reachable ordinarily stable state. Given those,

> **Theorem (weighted transfer).** Capacity-blocked weighted firing terminates
> from every initial state, and every capacity-terminal state it reaches is the
> ordinary normal form of that initial state.

*Proof.* Every capacity step is an ordinary step (legality includes
instability), so the capacity relation is a subrelation of a well-founded one
and therefore well-founded; a terminal state exists. By §5 that state is
ordinarily stable, and it is ordinarily reachable, so ordinary uniqueness
identifies it with the ordinary normal form. ∎

## 7. Sharpness

The bound cannot be lowered at any receiver with incoming multiplicity at least
two. The smallest witness has two vertices:

```
m(0,1) = 2,  m(1,q) = 1,  so d = (2,1),  max_u m(u,1) = 2.
Bound: C(1) >= 1 + 2 - 1 = 2.  Take C = (2,1), one below at vertex 1.
From x = (2,0): vertex 0 is blocked (x(1) + 2 = 2 > 1) and vertex 1 is stable,
so (2,0) is capacity-terminal; its ordinary normal form is (0,0).
```

Capacity has created a deadlock that ordinary firing does not have. Raising
`C(1)` to `2` removes it.

## 8. What is established and what is not

Established: §4, §5, §6 compile against Lean 4.35.0 with no `sorry` and axioms
`[propext, Classical.choice, Quot.sound]` only. Exact finite enumeration
corroborates the theorem and confirms sharpness; it does not prove it.

Not established when first written, and since settled (revision 0.6.0): that the bound is *necessary* at receivers of multiplicity one
beyond `C(v) >= d(v)`; cyclic graphs (the predecessor's cycle witness applies
unchanged); non-absorbing sinks; novelty. The capacity rule remains classical
finite-capacity Petri-net semantics and the ordinary theory is classical; only
the weighted threshold and its preservation argument are at issue.

## 9. The ordering hypothesis, restated (revision 0.5.0)

Sections 4–6 and the characterization of revision 0.3.0 both carry the ordering
as a *rank*: a function `Vertex n → Nat`, bounded by `n`, strictly increasing
along the relevant arcs. The rank exists only to supply a descent measure, and
carrying it has a cost: the step from "no such rank exists" to "an obstruction
exists" is then the classical finite-digraph fact that an acyclic finite
relation admits a topological order, which this dossier does not prove.

Taking the relation itself as the hypothesis removes the cost. Write

```
LiveArc v u   iff   Live u  and  Live v  and  mult u v > 0
```

so that `Acc LiveArc x` says that chasing blocked senders forward from `x`
terminates. Three things follow.

**Sufficiency needs no finiteness.** The proof of §5, read on `LiveArc`, is a
well-founded recursion with no appeal to the index bound. `n` survives only as
the type's parameter.

**The old hypotheses are a special case.** `n - rank` is a measure for
`LiveArc`, so a rank gives well-foundedness and the earlier theorem is an
instance.

**The obstruction comes from the hypothesis failing.** Suppose `LiveArc` is not
well founded. Some vertex `w` is not accessible. Then there is an arc from `w`
to a vertex that is also not accessible — if every `LiveArc`-predecessor of `w`
were accessible, `Acc.intro` would make `w` accessible. Take membership in the
filled set to be non-accessibility and that arc as the successor map. A vertex
that is not live is accessible outright, because every `LiveArc y x` carries
`Live x`, so the witness is live without further assumption. Nothing is counted
and nothing is ordered.

Hence, under live-closure, `LiveArc` is well founded exactly when no filled set
exists; the sufficient conditions and the obstruction are two readings of one
statement. What remains imported is only that a *finite acyclic* live subgraph
is well founded, which is what lets an exhaustive census decide the hypothesis
by cycle detection. That is a property of the decision procedure, not a step in
any proof here.
