# Written argument

There is no proof of any conjecture here. This dossier records exact
computations and simulations bearing on Hopkins–McConville–Propp Conjectures
21, 25, 26 and 27. The only proved statement is the reduction in §2, which
makes the loop computations exact.

## 1. Odd `n` on `ℤ` (Conjectures 26 and 27)

**Exactness of the probability computation.** The unlabeled process is
confluent. So every run from `n` chips at 0 has the same number of firings,
and the labeled states can be propagated layer by layer with their
probabilities. A protocol-2 step from state `s` picks an unstable site
uniformly, then a pair at it uniformly. A protocol-1 step picks uniformly among
all (site, pair) moves. The sorted outcome puts chip `k` at `k − m − 1`.

## 2. The two-colour criterion for sorting (loops and parallel edges)

Let `G` be `ℤ` with `ℓ_v` left edges, `m_v` loops and `r_v` right edges at
each `v`. A labeled firing at `v` chooses `d_v = ℓ_v + m_v + r_v` chips at
`v`. It moves the `ℓ_v` smallest labels left and the `r_v` largest right, and
keeps the `m_v` middle ones (HMP §3). Fix `t ∈ {1, …, n − 1}` and colour
labels `≤ t` red and the others blue. A colour state records the number of red
and blue chips at each site.

**Lemma (projection and lifting).**

(a) Projection. Let a labeled firing at `v` choose `k` red chips. In its
projection, the left neighbour receives `min(k, ℓ_v)` red and `ℓ_v − min(k, ℓ_v)`
blue chips. Of the `m_v` chips that stay, `min(max(k − ℓ_v, 0), m_v)` are red.
The right neighbour receives `max(k − ℓ_v − m_v, 0)` red and the rest blue.
This holds because every red label is smaller than every blue label.

(b) Lifting. Let a colour state be the projection of a labeled state `L`, and
take any colour firing at `v` with `k` red chips. Some labeled firing from `L`
projects to it: choose any `k` red and `d_v − k` blue labels at `v`.

(c) Stability. A labeled state is stable iff its projection is, since both
conditions read "fewer than `d_v` chips at every `v`".

**Corollary.** `G` sorts `Δⁿ` iff, for every `t`, no colour state reachable
from `t` red and `n − t` blue chips at 0 is stable with a blue chip strictly
left of a red one.

*Proof.* Suppose a reachable stable labeled state `D` is unsorted. Then some
`i < j` have `D(i) > D(j)`. Take `t = i`. Chip `j` is blue and chip `i` is
red, so by (a) and (c) the projection of `D` is a reachable stable colour state
with a blue chip strictly left of a red one. Conversely, suppose a reachable
stable colour state has a blue chip at `p` and a red chip at `q > p`. By (b),
applied step by step from `Δⁿ`, and by (c), it is the projection of a reachable
stable labeled state. In that state some label `> t` sits at `p` and some label
`≤ t` sits at `q > p`, so it is unsorted. ∎

The testers `check_loops.py`, `loops_scan/zs.cpp` and `loops_scan/zsr.cpp`
enumerate the reachable colour states of each `t` exactly. The C++ testers use
a window of 48 sites, and they abort with `WINDOW_EXCEEDED` if a chip could
leave it. No scan aborted. The early-exit mode used by the converse scan stops
at the first unsorted stable colour state. By the corollary, that state already
certifies that `G` does not sort `Δⁿ`. As cross-checks, the Python tester agrees
with a direct labeled search on 120 small cases, and `zsr.cpp` at `r = 1`
reproduces `zs.cpp`'s full output on 290 cases.
