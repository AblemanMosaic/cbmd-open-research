# Revisions

| Version | Change |
|---|---|
| 0.1.0 | Exhaustive exact checks of forest and connected-subgraph negative correlation (coefficientwise in lambda) on all 2-connected graphs with 3..9 vertices and two multigraph families. |
| 0.2.0 | Added §4, a written proof of the small-`λ` law, with gate `SMALL_LAMBDA_LAW`. Applied the independent review's fixes. The claim now says `P ≥ 0` in general and `P(1) > 0` for edges in a common block. Multigraph counts are stated per pair of edge classes, with the edge-copy pairs they cover. The parallel-pair notation and the connectedness assumption for `C` are made explicit. Integer weights are exact only for forests. Pairwise correlation is distinguished from negative association. Added arXiv:2609.11578 and the unspecified computations of arXiv:2610.00549. Corrected the `fnc.c` comments. Reran both 9-vertex runs with the shipped sources. |
| 0.2.1 | Applied the independent review of §4 and Corollary 2: the converse direction of (ii), the univariate non-cancellation, a citation for "common circuit iff same component" (Oxley, Prop. 4.1.2), and the fact that `M` and `M*` have the same components. The non-loop hypothesis is dropped, loops are treated explicitly, and the relation to arXiv:2610.00549 is stated precisely. |
| 0.3.0 | Added an exact negative-association scan beyond pairs, with gate `NA_SMALL` and a positive control. |
