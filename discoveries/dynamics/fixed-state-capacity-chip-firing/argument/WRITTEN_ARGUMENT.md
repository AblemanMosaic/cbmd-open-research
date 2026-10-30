# Written argument

## 1. Model

Capacity-blocked chip-firing exactly as in `CBMD-DYN-WEIGHTED-CAPACITY-001`.
A vertex `u` may fire when it holds at least `outdegree u` chips and no
receiver `w` with `mult u w > 0` would exceed `capacity w`. Firing removes
`outdegree u` chips from `u` and adds `mult u w` to each `w`; the remainder of
the outdegree goes to the absorbing sink.

## 2. The star

Senders `1..k`, sender `i` holding `a_i > 0` chips with outdegree and capacity
`a_i`, all sent to the receiver `v`. `v` has outdegree and capacity `B > 0`
and sends to the sink.

**Reachable states (Lean: `reach_iff`).** Every reachable state is determined
by the set of senders that have fired and the receiver's fill `f`. A sender
can fire only once: afterwards it holds `0 < a_i` chips. It can fire exactly
when its bundle fits, `f + a_i ≤ B`. The receiver can fire only when
`f ≥ outdegree v = B`, which together with `f ≤ capacity v = B` means
`f = B`, and it then resets to `0`. So the reachable states are exactly the
bin runs.

**Bin runs are block decompositions (Lean: `run_iff_blocks`).** Every reset
closes a block of total exactly `B`. Conversely, blocks of total `B` can be
run one after another, because all bundles are positive, so no prefix of a
block exceeds `B`.

**The normal form.** Ordinary firing fires every sender once and `v`
`⌊Σa/B⌋` times, so the normal form has every sender empty and `Σa mod B` at
`v`. This is checked by the census. When `B | Σa` the normal form is the
all-fired state with `v` empty, and the empty open block forces the run to end
on a reset. Hence reachability of the normal form is equivalent to a partition
of the bundles into groups of total exactly `B` (Lean:
`normal_form_reachable_iff_partition`).

## 3. Complexity

**Hardness.** 3-PARTITION asks whether `3m` positive integers with total
`mB` split into `m` triples each of total `B`. With `B/4 < a_i < B/2` every
group of total `B` is a triple. It is NP-complete in the strong sense (Garey
and Johnson, 1975), so it stays NP-complete with the numbers in unary. Map an
instance to the star with these `a_i` and this `B`. The system has `3m + 1`
vertices, and its multiplicities and capacities are the instance's own
numbers, so the transformation is polynomial even in unary. By §2 the normal
form is reachable iff the instance is a yes-instance. So FIXED-GOOD is
strongly NP-hard, even restricted to stars, which are two-level DAGs.

**Membership.**
- *On stars:* a bin run has at most `2k` steps (`k` sender firings, at most
  `k` resets), so it is a polynomial certificate. FIXED-GOOD on stars is
  NP-complete.
- *In general:* every capacity-reachable state lies in the box
  `0 ≤ y ≤ C`, so a state takes polynomial space even with binary
  capacities. Reachability of a given state is then in NPSPACE = PSPACE
  (Savitch).

Whether general FIXED-GOOD is in NP is open. Ordinary firing vectors can be
exponential in the number of vertices on digraphs, even with unary
multiplicities (diamond chains double the count at each level), so the obvious
certificate is too long.

## 4. Where the hardness lives

The weighted transfer theorem says every ordered system with
`C(v) ≥ d(v) + max_u m(u,v) − 1` reaches the normal form from every admissible
state. The star violates this at `v` as soon as some bundle has size `≥ 2`,
because `C(v) = d(v) = B`. The census confirms the consistency: every
instance meeting the bound is good. The hard instances lie strictly below it.

## 5. The all-states question is easy

Quantifying over every admissible initial state turns the question into
terminal stability. That is decided in polynomial time, by a decider proved
correct in Lean (`decideTerminalStable`, weighted dossier revision 0.11.0).
Fixing the initial state is what costs: the adversary no longer chooses the
worst state, and the scheduler has to find a good order from the given one.
