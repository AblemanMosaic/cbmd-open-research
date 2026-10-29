# Problem contract: capacity-blocked chip-firing

## 1. Exact model

Let `V = {0,...,n-1}` be nonsink vertices and let `q` be an absorbing sink. A
directed loopless multigraph is represented by multiplicities `m(u,v)` for
`u,v in V`, and `m(u,q)`. Define

`d(u) = m(u,q) + sum_v m(u,v)`.

A capacity vector `C` has nonnegative integer entries. An admissible state is
`x in product_u {0,...,C(u)}`.

Vertex `u` may fire at `x` exactly when:

1. `x(u) >= d(u)`; and
2. for every nonsink receiver `v`, `x(v) + m(u,v) <= C(v)`.

On firing, `d(u)` chips leave `u`, `m(u,v)` arrive at each nonsink `v`, and
`m(u,q)` disappear into the sink. All transfers are simultaneous.

The cycle begins with graphs whose nonsink edges respect the order `u < v` and
from which every vertex reaches the sink. This gives a finite DAG and a simple
strictly decreasing weighted potential, so every firing sequence terminates.

## 2. Vocabulary

- A **normal form** is an admissible state with no legal firing.
- An initial state is **confluent** when every maximal firing sequence reaches
  the same normal form.
- The system is **globally confluent** when every admissible initial state is
  confluent.
- A **capacity conflict** is a one-step divergence in which two firings are
  individually legal but their combined incoming demand exceeds at least one
  receiver capacity.

## 3. Initial finite box

- simple ordered DAGs with `n <= 4` nonsink vertices;
- unit nonsink and sink edges;
- every nonsink vertex reaches the sink;
- `C(u)` ranges from `d(u)` to `d(u)+1` initially;
- every admissible state is checked;
- deterministic order: vertex count, edge count, capacity sum, graph encoding,
  capacity tuple, chip sum, state tuple.

The finite box may produce counterexamples and conjectures. It cannot establish
an unbounded theorem.

## 4. Candidate statements and disconfirmation

### H1 — unrestricted DAG confluence

Every capacity-blocked system in the initial DAG box is confluent.

**Disconfirmation:** one initial state with two distinct terminal normal forms.

This is intentionally strong and is expected to fail; its smallest failure
defines the obstruction study.

### H2 — no capacity-conflict sufficiency

If no reachable state from `x` contains a capacity conflict, then `x` is
confluent.

**Disconfirmation:** a state with no reachable capacity conflict and at least
two normal forms.

This is expected to follow from termination plus a local diamond argument, but
the precise definition must survive computation before proof work begins.

### H3 — receiver-disjoint sufficiency

If distinct nonsink vertices have disjoint sets of nonsink receivers, then the
system is globally confluent.

**Disconfirmation:** a receiver-disjoint graph and state with two normal forms.

### H4 — slack repair

A graph-local lower bound on receiver slack suffices to preserve both orders of
every pair of simultaneously legal firings.

**Disconfirmation:** the proposed bound passes pairwise diamonds but a longer
reachable divergence yields distinct normal forms.

## 5. Prior-art boundary

Ordinary chip-firing confluence, least action in abelian networks, and Newman's
lemma are prior art. A firing-count cap is also known in the directed
chip-firing literature. This cycle does not claim those ideas.

The receiver-storage legality condition is classical finite-capacity Petri-net
semantics. The candidate object under examination is the narrower
chip-firing-shaped subclass and its DAG/unit-edge preservation theorem. Absence
of an exact match from the bounded search performed so far is not a novelty
result; a targeted literature review remains required before any such claim.

## 6. Promotion ladder

1. `REFERENCE_OBSERVATION`: deterministic enumeration by one implementation.
2. `INDEPENDENT_FINITE_VERIFICATION`: a separately written transition checker
   reproduces the witness or finite theorem.
3. `WRITTEN_ARGUMENT`: all assumptions and classical dependencies explicit.
4. `SOURCE_BOUND_COMPILED`: Lean statement compiles without `sorry` against a
   pinned toolchain.
5. `NOVELTY_REVIEWED`: exact statement compared with relevant literature.

