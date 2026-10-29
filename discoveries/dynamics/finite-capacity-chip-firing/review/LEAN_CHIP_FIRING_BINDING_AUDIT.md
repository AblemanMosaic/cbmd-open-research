# Lean chip-firing binding audit

Date: 2026-10-29  
Scope: exact-source comparison for the FD-C1 ordinary-stabilization obligation

## Candidate formal source checked

- Dhyey Mavani and David Perkinson, *Formalizing chip-firing and
  Riemann--Roch for graphs in Lean 4*, arXiv:2606.16679:
  <https://arxiv.org/abs/2606.16679>
- Public source repository:
  <https://github.com/DhyeyMavani2003/chip-firing-with-lean>
- Exact modules inspected:
  `ChipFiringWithLean/Basic.lean` and
  `ChipFiringWithLean/Algorithms.lean` on the repository's `master` branch.

## Finding

The development is a serious, maintained Lean formalization, but it does not
directly instantiate FD-C1. Its foundational object is a loopless **undirected
multigraph**, its chip configurations are integer-valued divisors, and its main
theory concerns firing equivalence, reduced divisors, and graph
Riemann--Roch. The algorithms module labels its executable reduction routines
as exploratory and states that the main proof does not depend on them.

FD-C1 instead needs natural-valued ordinary stabilization on a finite
**directed acyclic graph with an absorbing sink**, using a concrete simultaneous
unit-edge update. Importing the cited development would therefore require a
nontrivial transport theorem rather than discharge the obligation directly.

## Decision

The workspace proves the required ordinary theorem locally against the exact
FD-C1 update:

1. lexicographic decrease in topological order proves termination;
2. distinct legal firings commute, with natural-subtraction side conditions
   discharged from legality;
3. a compiled terminal form of Newman's lemma yields unique stabilization;
4. the existing transfer theorem then identifies every capacity terminal with
   that ordinary stabilization.

This decision is about exact type and theorem fit. It is not a criticism of the
cited formalization and it supplies no novelty evidence for FD-C1.

