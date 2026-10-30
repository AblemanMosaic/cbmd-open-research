# Neutral and negative results from the cost line

The corrections policy gives negative results the same durable treatment as
positive ones. Three outcomes from this line were recorded in the source ledger
but had no individual public export. They are stated here, bound to the evidence
already vendored under `verification/reference-model/`.

Each is a result **about the reference evaluator** under the declared arithmetic
cost model. None is a native or SAT statement.

## N1 — The row-assembly identity is exact but arithmetically neutral

The source row admits the closed assembly

```
row(u,y) = [y = u] - (n / 2^(R-1)) * (1 - prod_{s in E} (1 - x/(s+1)))
```

computable from the amplitude in `O(|E|^2)` ring operations. It is exact: it
reproduces the frozen producer on **10,476** orbit rows over the rationals and
`Z/25`, with zero mismatches.

It is **not** an arithmetic improvement. Ring-operation totals over that box are
**120,876** for the closed route against **123,588** for the reference Lagrange
route — a 2.2% difference, not a complexity gain. The session hypothesis that
the closed route would be `O(|E|^2)` against a reference `O(|E|^3)` was **wrong**:
both are quadratic in `|E|`.

What the identity does remove is the per-row numerator enumeration: 80,628
indicator tests over the same box. That saving belongs to the amplitude table
(N2), not to the polynomial arithmetic.

## N2 — The amplitude table is where the saving actually is

Because the amplitude depends only on `(delta, f)`, one table of at most `Q*R`
integers serves every target and every orbit column at fixed `(A,R,Q)`:

| `(A,R,Q)` | entries | mul / div / add | peak bits | enumeration tests replaced *per amplitude* |
|---|---|---|---|---|
| (17,5,80) | 390 | 3,150 / 1,580 / 1,180 | 22 | 24,685,131 |
| (15,8,80) | 612 | 7,776 / 4,368 / 2,796 | 34 | 389,575,972,971 |
| (7,4,40) | 154 | 1,016 / 472 / 390 | 15 | 76,155 |

This is the one clean positive outcome of the line, and it is recorded here only
to locate N1 correctly: the gain is in not enumerating, not in assembling.

## N3 — Row-centric evaluation loses at realistic sizes

A row-centric pass computes every owner's sum for a fixed target in one sweep
over the live columns; the owner-centric candidate route costs one candidate
construction and lookup per requested owner. Exact live-column counts give the
crossover directly:

| `(A,R,Q)` | `delta` | live columns | row-centric wins only if |
|---|---|---|---|
| (17,5,80) | 6 | 63 | `|V| > 63` |
| (17,5,80) | 39 (centred) | 584,936 | `|V| > 584,936` |
| (17,5,80) | 80 | 25,706,997 | `|V| > 2.6e7` |
| (15,8,80) | 38 (centred) | 51,738,692 | `|V| > 5.2e7` |

At the typical mismatch count the owner-centric design is right by five or more
orders of magnitude. Row-centric wins only for small `delta`. **This is a
negative result and is published so the idea is not rebuilt.**

## Scope

Ring-operation counts are counts in the reference `Ring` class, not bit costs.
The declared bit-cost model applies to the integer table only. No wall-clock
claim, no whole-cell or consumer cost, no native evaluator, no novelty
determination.
