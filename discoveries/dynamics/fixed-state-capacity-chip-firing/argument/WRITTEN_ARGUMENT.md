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

## 6. Getting stuck on the star (revision 0.2.0)

FIXED-BAD asks whether some capacity-legal run from `x` ends in a terminal
state that is not ordinarily stable. On the star this means: some bin run
stops with fill `f < B`, at least one sender unfired, and no unfired bundle
fitting (`bad_terminal_reachable_iff`).

**The fill is a residue (Lean: `fill_eq_mod`).** By `run_iff_blocks`, the
fired list is a sequence of closed blocks, each of total `B`, followed by an
open block of total `f`. So if `f < B`, then `f = (Σ_{i∈L} a_i) mod B`.

**A stuck run gives a residue witness (Lean: `stuck_imp_witness`).** Call a
set `F` of senders a *residue witness* when `F` leaves out at least one sender
and every sender `i ∉ F` satisfies `(Σ_F a) mod B + a_i > B`. A stuck run's
fired set is one. The condition involves no order and no packing, only a
residue. Its contrapositive is a **certificate of safety** (Lean:
`safe_of_no_witness`): if no residue witness exists, no reachable terminal
state is bad.

**Deciding the witness condition in pseudo-polynomial time (written; checked
against the definition).** Sort the bundles `v_1 ≤ … ≤ v_k`. Suppose `F` is a
witness, and let `j` be the first unfired position. Every earlier position is
fired. Every unfired bundle is at least `v_j`, so the condition for all of them
follows from the condition for `j`. Conversely, take any `j` and any subset `X`
of the positions after `j`, with `(v_1 + … + v_{j−1} + Σ_X v) mod B + v_j > B`.
Then `F = {1, …, j−1} ∪ X` is a witness: `j` is unfired and every unfired
bundle is at least `v_j`. The residues reachable by subsets of a suffix can be
tabulated right to left in `O(kB)` time. So the witness condition is decided in
`O(kB)` time after sorting. That is polynomial when the numbers are written in
unary, and pseudo-polynomial in general.

**The converse is a conjecture.** *Every residue witness is realised by a
stuck run.* If it holds, FIXED-BAD on stars is decided in pseudo-polynomial
time, while FIXED-GOOD on stars is strongly NP-hard (§3). The asymmetry would
be complete: "can it end badly?" would be easy where "can it end well?" is hard.

Evidence (`verification/reference/residue_witness.py`,
`evidence/residue_witness.json`): every multiset of bundles with `B ≤ 13`,
`k ≤ 8` and entries `1..B` (`1..B+1` for `k ≤ 4`, which covers bundles too big
ever to fire) — 500,461 instances, of which 496,470 (99.2%) have a reachable stuck run and exactly those 496,470 have a residue witness; no counterexample in either direction. The pseudo-polynomial decider agrees with the definition on all of them. The bin-run search agrees with the weighted
dossier's exact simulator on 400 random stars. The controls each bite:

- requiring the stuck run to stay inside one bin misses stuck runs, so closed
  blocks matter;
- weakening `>` to `≥` accepts instances with no stuck run;
- largest-fit and smallest-fit greedy runs each miss stuck runs that exist.

**Why the converse is not proved here.** The natural route fails. One would
take a witness, fire its set, and hope the order works out, but a witness's
fired set need not pack into exact blocks, and the realising run often uses a
different witness. The obvious extremal choices also fail in range:

- the witness with the most unfired senders;
- the witness with the fewest;
- choosing the witness of least fired total and hoping *every* order of its
  fired set packs. This held up to `B ≤ 10, k ≤ 6` and fails in the larger
  range (11 instances).

The weaker form held everywhere in range. Some least-total witness has a fired
set that *some* order packs into closed blocks plus the open block (0
failures). In fact the **largest-fit** order does: repeatedly fire the largest
fired-set bundle that fits (0 failures). Smallest-fit fails. So a sharper
conjecture is that, for a witness of least fired total, firing its set
largest-fit-first never gets stuck before the set is exhausted. The run then
ends at fill `(Σ_F a) mod B`, with every unfired bundle blocked. That would prove the conjecture, but it needs an argument
this revision does not have.

**Binary encoding.** With the numbers in binary, the witness condition is a
subset-residue problem with a window. Whether FIXED-BAD on stars is NP-hard in
that encoding is not determined here.
