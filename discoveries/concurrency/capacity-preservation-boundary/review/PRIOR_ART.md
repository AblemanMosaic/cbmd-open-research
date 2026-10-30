# Prior art

A bounded search against the Petri-net literature, run after revisions 0.2.0
through 0.5.0 were compiled. It is not a specialist assessment and does not
settle novelty; it settles **vocabulary and framing**, which matters more here,
because three of the four results turn out to be standard objects wearing
unfamiliar names, and one of them is less surprising than it first looked.

## The vocabulary this dossier should have been using

Two corrections, adopted in the README and the argument.

**Strict and weak transition rules.** What this dossier calls *capacity
enabled* and *ordinarily enabled* are Murata's **strict** and **weak**
transition rules for finite-capacity nets. `PRESERVES(N, C)` is therefore the
question: *does the strict rule admit a dead marking that the weak rule does
not?*

> Tadao Murata, *Petri Nets: Properties, Analysis and Applications*,
> Proc. IEEE 77(4):541–580, 1989.
> <https://elearning.unimib.it/pluginfile.php/1372798/mod_resource/content/2/Petri%20Nets%20analysis%20and%20applications.pdf>

Murata's Theorem 1 states that a **pure** finite-capacity net under the strict
rule and its complemented net under the weak rule have the same firing
sequences from a fixed initial marking. That is an equivalence between two
*models of the same capacitated net*; it says nothing about the capacitated net
against the **uncapacitated** one, which is the comparison this dossier makes,
and it carries no analogue of the all-full witness.

**The obstruction is a trap.** The set `S` of revision 0.3.0 — every transition
consuming from a member produces into a member — is a **trap** in the original
net, and dually a **siphon** in the complemented net. That dualization is
standard. The only departure is the zero-capacity branch of clause 3, which
lets a place that can never hold a token act as a sink for the trap condition.

> Faten Nabli, François Fages, Thierry Martinez, Sylvain Soliman,
> *On enumerating minimal siphons in Petri nets using CLP and SAT solvers*,
> Constraints 21(2), 2016. <https://ar5iv.arxiv.org/html/1304.2948>

Using words the field already has is not a concession; it is the only way the
statements here can be compared with what is known.

## Result by result

### Revision 0.2.0 — the all-full obstruction

No prior theorem of the form *"capacity does or does not introduce deadlock"*
was located, under that description or as "spurious" or "artificial" deadlock.
But the statement is a one-line argument on the witness `m = C`, and **no
weight should be claimed for it**. Its value is explanatory: it says why
chip-firing needs a sink, not that it is hard to prove.

### Revision 0.3.0 — the flow characterization

The substance is trap/siphon duality, which anyone in the field would
recognize on sight. What could **not** be found is the reachability-free exact
**iff**. Every formulation located quantifies over *reachable* markings and
therefore yields an implication plus a sufficient condition:

- Murata Theorem 15 (asymmetric choice: live *if* every siphon contains a
  marked trap — explicitly "if, but not only if");
- Commoner's theorem, <https://ar5iv.labs.arxiv.org/html/2401.12067>;
- Feng Chu and Xiao-Lan Xie, *Deadlock analysis of Petri nets using siphons and
  mathematical programming*, IEEE T-RA 13(6):793–804, 1997;
- Jörg Desel and Javier Esparza, *Free Choice Petri Nets*, CUP 1995, which
  defines a dead marking without reachability (Def. 2.7) but gives no
  structural iff. <https://www.model.in.tum.de/~esparza/bookfc.html>

So the exactness here comes from **dropping reachability**, which is what turns
the classical one-way implication into an equivalence. Whether that structural
iff is written down somewhere remains **unresolved**; it is folklore-adjacent
and should not be cited as novel.

### Revision 0.5.0 — the weighted level version

The monotone closure is the classical maximal-trap fixpoint. Existence of a
siphon, and finding one, is known to be polynomial (Cordone, Ferrarini and
Piroddi 2003, as recorded by Nabli et al.), and a polynomial algorithm for a
minimal siphon is older still:

> S. Tanimoto, M. Yamauchi, T. Watanabe, *Finding Minimal Siphons in General
> Petri Nets*, IEICE Trans. Fund. E79-A(11):1817–1824, 1996.
> <https://globals.ieice.org/en_transactions/fundamentals/10.1587/e79-a_11_1817/_p>

The **algorithm is textbook**. The level-valued generalization — thresholds in
place of membership, forced by weighted arcs — was not found, and is
**unresolved** rather than claimed.

### Revision 0.4.0 — the complexity dichotomy

Two things must be said plainly here.

**This is not the classical deadlock problem, and the contrast is the point.**

> Allan Cheng, Javier Esparza, Jens Palsberg, *Complexity Results for 1-safe
> Nets*, Theoretical Computer Science 147:117–136, 1995.
> <https://archive.model.in.tum.de/um/bibdb/esparza/tcs95.pdf>

Deadlock for 1-safe nets is **PSPACE-complete** there (Thm 7), and
NP-complete for 1-safe free-choice nets (Thm 14). Those problems ask whether
some **reachable** marking is dead. The question here quantifies over all
admissible markings and has no reachability in it, which is exactly why it
lands in coNP rather than PSPACE. The gap between PSPACE and coNP is the cost
of reachability, not a sharper analysis of the same problem, and this dossier
should never be read as improving on that line of work.

**The reduction is a standard template.** Encoding SAT into a siphon-shaped
condition is established practice; NP-completeness of finding a minimal siphon
containing a given set of places is proved by reduction from 3-SAT in

> M. Yamauchi, T. Watanabe, *Time complexity analysis of the minimal siphon
> extraction problem of Petri nets*, IEICE Trans. Fund. E82-A(11):2558–2565,
> 1999.

The clause-to-transition encoding used in revision 0.4.0 is of the same family.
What was not found elsewhere is the specific problem — *a capacity-dead but not
ordinarily dead marking exists* — and the **one-input versus two-input
dichotomy**. Those are plausibly new, and **low-surprise**: the boundary sits
where it always sits once enabledness becomes a conjunction.

coNP **membership** is immediate and is claimed as nothing more.

*Added with revision 0.10.0.* The hardness also holds for strict free-choice
nets with all capacities 1. Cheng–Esparza–Palsberg Thm 14 (reachable deadlock,
NP-complete for free-choice nets) is the parallel result for the reachability
question; neither implies the other, for the reason given above.

## The state-machine query, run — and it lands

The bounded search named capacities over **state machines** (one input, one
output per transition) as its highest-value open query, because that is exactly
the subclass revision 0.3.0 characterizes. Running it moves that result from
"unresolved" towards "known", in a literature the Petri-net search did not
reach: closed queueing networks with finite buffers and blocking.

> Jörg Liebeherr and Ian F. Akyildiz, *Deadlock Properties of Queueing Networks
> with Finite Capacities and Multiple Routing Chains*.
> <https://www.comm.utoronto.ca/~jorg/archive/papers/CS-93-65.pdf>

Their Theorem 1 is a **necessary and sufficient** deadlock-freedom condition
for a closed network under blocking-after-service: for every *buffer cycle* `C`
some chain `r` satisfies `Σ_{i ∈ S(C)_r} φ(B_ir) + |S(C)_r| > K_r`. A station
with a full destination buffer is blocked, a cycle of such stations is a
deadlock, and Lemma 2 identifies buffer cycles with cycles in a directed graph
on buffers. That is the same obstruction as revision 0.3.0 in its single-output
case: a cycle of full places, each blocked by the next.

Three differences, and only the third is in this dossier's favour.

1. **Their condition carries a job count.** `K_r` is the number of jobs in
   chain `r`, which is conserved. The condition is about whether a cycle *can*
   be filled given how many jobs exist — reachability information, in the only
   form a closed network admits. A capacitated Petri net with drains has no
   conservation law, so no such term appears here, and the condition degenerates
   to pure structure.
2. **Theirs is a cycle, mine is a closed set.** With one output per transition
   a set closed under successors contains a cycle, so the two agree in that
   case. With several outputs they do not: closure is strictly stronger than a
   cycle, which is why revision 0.6.0 is not simply a restatement of this.
3. **Theirs is for a fixed closed network; drains and zero capacities do not
   occur.** Clause 2 (no drain takes from a member) and the zero-capacity
   branch of clause 3 have no counterpart there.

So the honest reading: **for unit-weight, single-output, conservative nets, the
obstruction of revision 0.3.0 is known**, as a cycle of full buffers, with an
exact iff that has been in the queueing literature since the early 1990s. The
"exact iff without reachability" that the Petri-net search could not locate is
not a gap in the literature; it is what that condition becomes when
conservation is dropped. Revision 0.3.0 should be read as a Petri-net-side
restatement in a setting with drains, not as a new characterization.

What this does not cover, and what revisions 0.5.0 and 0.6.0 therefore retain:
weighted arcs, several outputs per transition, zero-capacity places, and the
complexity dichotomy.

## What this search did not settle

- The full text of Yamauchi and Watanabe 1999 was not obtained, so their 3-SAT
  reduction has not been compared against revision 0.4.0's directly.
- Whether Liebeherr and Akyildiz's Theorem 1, or an earlier result in the same
  line, also covers the non-conservative case. The paper itself is framed
  entirely around closed networks. Kundu and Akyildiz, *Deadlock free buffer
  allocation in closed queueing networks*, <https://link.springer.com/article/10.1007/BF01150855>,
  is the nearest predecessor and was not fetched.
- Whether the reachability-free iff is folklore. A specialist would likely
  answer this in one sentence.

## Standing

No claim in this dossier is a novelty claim, and the second search weakened
the position rather than strengthening it.

- The obstruction is a **trap** (dually a siphon), and the monotone closure is
  the classical maximal-trap fixpoint. Standard.
- For unit-weight single-output conservative nets the characterization is
  **known**, as a cycle of full buffers with an exact iff, in the
  queueing-with-blocking literature. The absence of reachability here is the
  degenerate case of their job-count condition, not a new vantage point.
- The all-full obstruction is a one-line argument, claimed only as
  explanatory.
- What is not accounted for by either literature: weighted arcs, several
  outputs per transition, zero-capacity places, and the one-versus-two input
  complexity dichotomy — whose hardness side nonetheless uses a standard
  reduction template.

What this dossier can claim without qualification is the **form** of the
evidence: compiled proofs with recorded axiom dependencies, procedures that
emit certificates a separate checker validates, and ablations showing each
condition is load-bearing.

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
