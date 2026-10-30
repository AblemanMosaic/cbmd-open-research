# Review

No external review.

A bounded prior-art search was run after revisions 0.2.0 through 0.5.0 were
compiled, and is recorded in [`PRIOR_ART.md`](PRIOR_ART.md) with citations and
the queries used. It changed the framing of this dossier in three ways:

- the two enabledness notions here are Murata's **strict** and **weak**
  transition rules, and the dossier now uses those words;
- the obstruction is a **trap** in the original net, dually a **siphon** in the
  complemented net — standard objects, for which no novelty is claimed;
- the coNP-completeness of revision 0.4.0 is **not** comparable to the
  PSPACE-completeness of deadlock for 1-safe nets, because that problem
  quantifies over reachable markings and this one does not.

What the search did not settle, and what is still owed:

- whether the reachability-free exact **iff** is folklore. Every formulation
  located quantifies over reachable markings and gives an implication plus a
  sufficient condition, never an equivalence. A specialist would likely settle
  this in a sentence.
- a targeted search on capacities over **state machines** — one input and one
  output per transition — which is exactly the subclass revision 0.3.0
  characterizes. None was located. This is the highest-value next query and
  may close that question in the negative.
- direct comparison against the 3-SAT reduction of Yamauchi and Watanabe 1999,
  whose full text was not obtained.

The earlier note stands and is subsumed: the nearest named notions before the
search were **implicit places** (capacities that never restrict firing, which
is strictly stronger than what is studied here and is the trivially sufficient
case) and **non-blockingness** of bounded nets, a reachability property rather
than a structural condition on capacities.
