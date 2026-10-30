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
