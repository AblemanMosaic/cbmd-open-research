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

**Partial converse (Lean: `realise_small`, `realise_pair`,
`bad_of_small_or_pair_witness`; revision 0.3.0).** Suppose a residue witness
leaves unfired a set `U` that totals at most `B`, or has exactly two members.
Then some run gets stuck.

The proof is by strong induction on the total of the unfired bundles. It runs
from any reachable state with an empty receiver, so closing an exact block
gives a smaller instance of the same statement. Write `F` for the witness's
fired part, `r = (Σ_F a) mod B`, and suppose no run gets stuck. Five general
facts follow.

1. *No exact block inside `F`.* Otherwise close it first. The residue and `U`
   are unchanged, and the induction hypothesis applies.
2. *`Σ_F a ≥ B`.* Otherwise firing all of `F` in one bin already gets stuck.
3. *Every maximal one-bin packing is exact.* A non-exact maximal packing that
   leaves something unfired is a stuck run.
4. *Room.* Every subset of `F` of total at most `B` leaves room for some bundle
   of `U`. Extend it to a maximal subset `G` of `F`. Then extend `G` to a
   maximal packing of everything; that packing is exact by (3), so it must add
   bundles, and those come from `U`.
5. *Small rest.* If the remaining senders contain no exact block, they total
   less than `B`. Otherwise a maximal packing of them is a stuck run.

*Case `Σ_U a ≤ B`.* Pack `U` first and extend to a maximal packing `E`. By (3),
`E` is exact, so `F` contributes `B − Σ_U a` to it. What remains after closing
`E` lies inside `F`. By (1) it is exact-free, so by (5) it totals less than
`B`, and by (4) at most `B − a_u` for some `u ∈ U`. Then
`Σ_F a ≤ 2B − Σ_U a − a_u < 2B − a_u`. But `B ≤ Σ_F a < 2B` forces
`Σ_F a = B + r > 2B − a_u`, because `r + a_u > B`.

*Case `U = {u, v}` with `a_u + a_v > B`.* Take a maximal subset `G` of `F`.
By (4) some `x ∈ U` fits on it. Then `G ∪ {x}` is maximal, because the other
bundle `y` overflows (`a_x + a_y > B`), so it is exact. In the remaining
instance, a maximal subset `G'` of `F \ G` must take `y` on top; otherwise it
is a stuck packing. `G' ∪ {y}` is again exact, since it cannot exhaust what
remains (that would make `Σ_F a < B`). What remains then lies in `F`. By (1),
(4) and (5) it totals at most `B − a_z` for some `z ∈ U`, so
`Σ_F a ≤ 3B − (a_u + a_v) − a_z < 2B − a_z`, the same contradiction.

**Coverage.** In the exhaustive range (`B ≤ 13, k ≤ 8`), 492,524 of the 496,470 instances with a witness have a witness of one of these two shapes. For those instances the converse is now proved, not conjectured, and `residue_witness.py` checks the theorem against the model on every one of them. The other 3,946 instances, including those with a bundle too big ever to fire, rest on the conjecture. What is left open is instances in which every
witness leaves at least three senders unfired, with total above `B`.

**Further search.** `verification/reference/bin_runs_exhaustive.c` is optional
and needs a C compiler. It uses `fill_eq_mod` to take the fired mask alone as
the state. It found no counterexample on these ranges: all multisets with
`B ≤ 30, k ≤ 7`; `B ≤ 23, k ≤ 9`; `B ≤ 18, k ≤ 10`; `B ≤ 14, k ≤ 12`; and
400,000 random instances with `10 ≤ B ≤ 100`, `9 ≤ k ≤ 16`. The output is in
`evidence/bin_runs_exhaustive.txt`.

**A one-step reduction (unproved).** The conjecture would follow by induction
from this lemma: *if every maximal one-bin packing is exact and a witness
exists, then some exact block can be closed so that a witness survives.* A
search found no violation for `B ≤ 20, k ≤ 10`, but the lemma is not proved
here.

**Why the full converse is not proved here.** The natural route fails. One would
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

**The conjecture is specific to one receiver.** With several receivers, the
same reasoning shows that each receiver's fill is the residue of its own fired
total. So a stuck run still yields a vector residue witness, and the condition
is still necessary. It is not sufficient. Take five senders whose bundles split
between two receivers of capacity 4 and 6 as `(3,1), (1,2), (3,3), (0,2),
(0,1)`. The set {1st, 3rd, 5th} is a witness: residues `(2, 5)`, and both
other senders overflow the second receiver. Yet exact simulation finds only one
terminal state, the normal form. To realise the witness, the first receiver
would have to close a block of 4 after the first sender's 3, and the only
bundle that can supply that 1 belongs to a sender the witness leaves unfired.
Random search found this instance among 23,741 two- and three-receiver
systems. It is checked against the weighted dossier's simulator in
`residue_witness.py`.

**Binary encoding.** With the numbers in binary, the witness condition is a
subset-residue problem with a window. Whether FIXED-BAD on stars is NP-hard in
that encoding is not determined here.
