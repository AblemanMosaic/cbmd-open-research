# Negative edge correlation for forests and connected subgraphs: exhaustive checks to 9 vertices

> **Standing:** `CONJECTURE`, `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-COMB-FOREST-NC-001`

## The question

Let `G` be a finite graph. Pick a forest of `G` uniformly at random, or with
probability proportional to `λ^{#edges}`. Are two distinct edges `e`, `f`
negatively correlated, that is, `P(e and f) ≤ P(e)·P(f)`? Kahn (2000) and
Grimmett–Winkler (2004, Conjecture 1.1) conjecture yes. They conjecture the
same for a uniformly random connected spanning subgraph. Both questions have
been open for over twenty years. Spanning trees are the classical exception:
there, negative correlation holds by Kirchhoff's theorem.

Before this dossier, the published computer checks were limited:

- **Forests:** Grimmett–Winkler checked all simple graphs on at most 8
  vertices, and those on 9 vertices with at most 18 edges.
- **Connected subgraphs:** only planar-dual consequences of the forest check.

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
So, for both models, on every graph with at most 9 vertices:

- the uniform measure is edge-negatively correlated;
- so is the `λ`-weighted measure, for every `λ > 0` (Kahn's weighted form for
  forests, and the `q → 0` random-cluster form for connected subgraphs).

**Multigraphs.** Grimmett–Winkler call multigraphs "more interesting". The
same holds, with all coefficients nonnegative, on:

- all multigraphs with edge multiplicity at most 3 on the 2-connected
  6-vertex graphs: 1,450,016 multigraphs, 100,776,619 pairs, including
  parallel pairs;
- all multigraphs with multiplicity at most 2 on the 2-connected 7-vertex
  graphs: 2,016,427 multigraphs, 213,200,562 pairs.

Both multigraph families were run for forests and for connected subgraphs.

| Vertices | 2-connected graphs | Edge pairs | Forests: violations | Connected: violations |
|---|---|---|---|---|
| 3–7 | 538 | 37,531 | 0 | 0 |
| 8 | 7,123 | 827,928 | 0 | 0 |
| 9 | 194,066 | 34,342,886 | 0 | 0 |

Here "violation" means `P_X(1) < 0` or a negative coefficient. Neither ever
occurs.

## What is not established

- A proof of either conjecture for any infinite class beyond those already in
  the literature.
- Graphs on 10 or more vertices. A resumable run over the 9,743,542
  2-connected 10-vertex graphs (forests) is in progress and is not claimed.
- General real edge weights (Grimmett–Winkler (1.7)) beyond the integer
  weights realised by multiplicities at most 3.
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
