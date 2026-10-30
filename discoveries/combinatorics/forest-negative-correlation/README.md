# Negative edge correlation for forests and connected subgraphs: exhaustive checks to 9 vertices

> **Standing:** `CONJECTURE`, `EXACT_MODEL_VERIFIED`, `PROVISIONAL_WRITTEN_ARGUMENT` (small-`λ` theorem)

Permanent claim ID: `CBMD-COMB-FOREST-NC-001`

## The question

Let `G` be a finite graph. Pick a forest of `G` uniformly at random, or with
probability proportional to `λ^{#edges}`. Are two distinct edges `e`, `f`
negatively correlated, that is, `P(e and f) ≤ P(e)·P(f)`? Kahn (2000)
conjectures yes, and Grimmett–Winkler (2004, Conjecture 1.1) conjecture the
stronger negative association. Only the pairwise correlation is checked
here. They conjecture the
same for a uniformly random connected spanning subgraph. Both questions have
been open for over twenty years. Spanning trees are the classical exception:
there, negative correlation holds by Kirchhoff's theorem.

Before this dossier, the published computer checks were limited:

- **Forests:** Grimmett–Winkler checked all simple graphs on at most 8
  vertices, and those on 9 vertices with at most 18 edges.
- **Connected subgraphs:** only planar-dual consequences of the forest check.
- **2026:** Çiçeksiz–Ravichandran (arXiv:2610.00549) mention "exact
  coefficientwise computations" without stating which graphs. They may
  overlap with this dossier.

## What this dossier records (evidence, no proof)

Write `X` for the forest polynomial `Z` or the connected-subgraph polynomial
`C`. Negative correlation of `e`, `f` at weight `λ` is equivalent to

    P_X(λ) = X_{G/e} X_{G/f} − X_G X_{G/e/f} ≥ 0.

`P_X` is an integer polynomial, computed exactly
(`argument/WRITTEN_ARGUMENT.md`, §1). It suffices to check 2-connected graphs
(§2).

**Result.** Take every 2-connected simple graph on 3 to 9 vertices
(1 + 3 + 10 + 56 + 468 + 7,123 + 194,066 graphs, OEIS A002218) and every pair
of distinct edges, 35,208,345 pairs in all. For both forests and connected
spanning subgraphs, every coefficient of `P_X` is nonnegative, and `P_X(1) > 0`.
Edges in different blocks give `P_X ≡ 0`, which means independence. So, for
both models, on every graph with at most 9 vertices (connected, for the
connected-subgraph model):

- the uniform measure is edge-negatively correlated;
- so is the `λ`-weighted measure, for every `λ > 0` (Kahn's weighted form for
  forests, and the `q → 0` random-cluster form for connected subgraphs).

**Multigraphs.** Grimmett–Winkler call multigraphs "more interesting". The
same holds, with all coefficients nonnegative, on:

- all multigraphs with edge multiplicity at most 3 on the 2-connected
  6-vertex graphs: 1,450,016 multigraphs and 100,776,619 pairs of edge
  classes, including parallel pairs, which cover 381,037,850 pairs of edge
  copies;
- all multigraphs with multiplicity at most 2 on the 2-connected 7-vertex
  graphs: 2,016,427 multigraphs and 213,200,562 pairs of edge classes, which
  cover 461,730,002 pairs of edge copies.

Copies in a class are interchangeable, so one representative pair per pair of
classes suffices.

Both multigraph families were run for forests and for connected subgraphs.

| Vertices | 2-connected graphs | Edge pairs | Forests: violations | Connected: violations |
|---|---|---|---|---|
| 3–7 | 538 | 37,531 | 0 | 0 |
| 8 | 7,123 | 827,928 | 0 | 0 |
| 9 | 194,066 | 34,342,886 | 0 | 0 |

Here "violation" means `P_X(1) < 0` or a negative coefficient. Neither ever
occurs.

## A proved statement: the small-`λ` law

`argument/WRITTEN_ARGUMENT.md`, §4, proves the following for every matroid, and
so for every multigraph. Let `e`, `f` be two edges, and let `L` be the length
of a shortest cycle through both. Then the Rayleigh difference satisfies

    P_Z(λ) = N λ^{L−2} + O(λ^{L−1}),

where `N` is the number of shortest cycles through `e` and `f`. If no cycle
contains both, `P_Z ≡ 0`. So the weighted forest measure is strictly negatively
correlated for all small enough `λ > 0`, whenever `e` and `f` share a block.
The matroid statement replaces cycles by circuits.

Applied to the bond matroid, the same theorem gives a large-`λ` law for
connected subgraphs. The top term of `P_C` is `N* λ^{2m − c* − 2}`, where
`c*` is the size of a smallest bond (minimal edge cut) through `e` and `f`,
`N*` is the number of such bonds, and `m` is the number of edges. So the
connected-subgraph measure is strictly negatively correlated for all large
enough `λ`.

The proof combines two facts. A coefficient depends only on the restriction
of the graph to the coefficient's support. On a restriction where `e` and `f`
lie in different blocks, the measure factorises, so the coefficient vanishes.
The law also matches all 37,531 edge pairs of all 2-connected graphs with at
most 7 vertices, and 5,040 element pairs of random matroids. Specialists may
well know it. It is recorded because it is the exact low-order counterpart of
the large-`λ` analysis of arXiv:2610.00549.

## What is not established

- A proof of either conjecture for any infinite class beyond those already in
  the literature.
- Graphs on 10 or more vertices. A resumable run over the 9,743,542
  2-connected 10-vertex graphs (forests) is in progress and is not claimed.
- General real edge weights (Grimmett–Winkler (1.7)). For forests, a class
  of `k` parallel copies acts like one edge of weight `kλ`, so the multigraph
  runs cover some integer weight ratios. For connected subgraphs there is no
  such exact correspondence.
- Negative association (beyond pairwise correlation).

## Reproduction

```text
python -B discoveries/combinatorics/forest-negative-correlation/verification/reference/check_forest_nc.py
cd discoveries/combinatorics/forest-negative-correlation/verification/reference
cc -O2 -o fnc fnc.c -lm && cc -O2 -o cnc cnc.c -lm
geng -Cq 9 | ./fnc        # forests, about 20 minutes on 2 cores (split with res/mod)
geng -Cq 9 | ./cnc        # connected subgraphs, about 20 minutes on 2 cores
geng -Cq 6 | multig -q -T -m3 | ./fnc -T
```

`geng` and `multig` are from nauty 2.8.8; the source ships inside the PyPI
package pynauty 2.8.8.1.
