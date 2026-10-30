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

## What this search did not settle

- The full text of Yamauchi and Watanabe 1999 was not obtained, so their 3-SAT
  reduction has not been compared against revision 0.4.0's directly.
- No source was located treating capacities on **state machines** — nets whose
  transitions have one input and one output — specifically. Revision 0.3.0 is
  exactly that subclass, so a targeted search there is the highest-value next
  step and may well close revision 0.3.0's novelty question in the negative.
- Whether the reachability-free iff is folklore. A specialist would likely
  answer this in one sentence.

## Standing

No claim in this dossier is a novelty claim. Three of the four results are
restatements of recognized objects — traps, siphons, and the maximal-trap
fixpoint — in a setting that removes reachability; what is specific here is
that removing it makes the condition exact, and that the exactness has a
compiled proof. The fourth is a complexity dichotomy whose hardness side uses
a standard reduction template and whose statement was not found elsewhere.
