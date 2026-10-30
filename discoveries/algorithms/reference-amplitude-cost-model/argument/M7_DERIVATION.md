# The master formula B5-M7, derived from the producer's definition

The cost theorem compares the frozen producer `literal_numerator` with

```
n(A,R,δ,f) = 2^(R−1) (−1)^A Σ_{k=0}^{d} C(N,k) C(A+d−k−1, d−k),    d = R−1−f,  N = A+R−δ,
```

and calls it "the proved identity B5-M7". That proof is in the sealed source
archive, not in this repository. This note gives a self-contained proof from
the producer's own definition, in four steps, each checked separately by
[`verification/independent/derive_m7.py`](../verification/independent/derive_m7.py).

**Setting.** `u` has length `2Q`. `swap(u,S)` exchanges `u[p]` and `u[Q+p]` for
`p ∈ S`. `D = {p : u[p] ≠ u[Q+p]}`, `δ = |D|`. The producer is called with `y` in
the swap orbit of `u`, `y = swap(u,M)`, and `t ∈ E = {p : y[p] ≠ u[Q+p]}`, with
`f = |E| − 1`. It sets `active = [Q] ∖ {t}`, `base = swap(u, active)`, and returns

```
n = Σ_{j<R} c_j 2^(R−1−j) Σ_{S ⊆ active, |S|=j} Σ_{B ⊆ S} (−1)^|B| [swap(base,B) = y]
```

where `c` solves `Σ_j C(A+i, j) c_j = (−1)^(A+i)` for `0 ≤ i < R`.

## Step 1 — the indicator collapses

**Claim.** For `B ⊆ active`, `[swap(base,B) = y] = [B ∩ D = E ∖ {t}]`.

Swaps commute and are involutions, so `swap(base,B) = swap(u, active ∖ B)`.
Swapping `p` changes `u` exactly when `p ∈ D`. Hence `swap(u,X) = swap(u,X')`
iff `X` and `X'` agree on `D`. So the indicator holds iff `active ∖ B` and `M`
agree on `D`. Now `E = D ∖ M`, so `t ∈ D ∖ M`, and `t` lies in neither set. For
`p ∈ D ∖ {t}`, `p ∈ B ⟺ p ∉ M ⟺ p ∈ E`. ∎

So the amplitude depends on `u`, `y` and `t` only through `δ` and `f`, which
is what the `Q·R` table of `ALGORITHMIC_EFFICIENCY.md` relies on.

## Step 2 — the inner sum collapses

With `E' = E ∖ {t}`, a set `B ⊆ S` has `B ∩ D = E'` iff `E' ⊆ S` and
`B = E' ∪ B'` with `B' ⊆ S ∖ D`. So

```
Σ_{B⊆S} (−1)^|B| [B ∩ D = E'] = (−1)^f [E' ⊆ S] [S ⊆ D].
```

The surviving `S` of size `j = f + i` choose `i` further elements of the
`δ − 1 − f` elements of `D ∖ {t} ∖ E'`. Therefore

```
n = (−1)^f Σ_{i=0}^{d} c_{f+i} 2^(d−i) C(δ−1−f, i).                         (S2)
```

## Step 3 — the parity coefficients in closed form

`P(x) = Σ_j c_j C(x,j)` is the polynomial of degree `< R` with
`P(A+i) = (−1)^(A+i)`. Newton's forward formula in `x − A`, with
`h(i) = (−1)^(A+i)` and `Δh = −2h`, gives `P(x) = (−1)^A Σ_k (−2)^k C(x−A, k)`.
Vandermonde's identity `C(x−A,k) = Σ_j C(x,j) C(−A, k−j)` and
`C(−A,m) = (−1)^m C(A+m−1, m)` give

```
c_j = (−1)^A (−2)^j Σ_{m=0}^{R−1−j} 2^m C(A+m−1, m).                        (S3)
```

## Step 4 — a change of variables

Substituting (S3) into (S2), the signs and powers of two combine to
`(−1)^A 2^(R−1)`, and

```
n = (−1)^A 2^(R−1) Σ_{i+m≤d} (−1)^i C(δ−1−f, i) 2^m C(A+m−1, m)
  = (−1)^A 2^(R−1) [x^d] (1−x)^(δ−2−f) (1−2x)^(−A).
```

For a formal power series `F`, `[x^d] F(x) = [z^d] F(z/(1+z)) (1+z)^(d−1)`.
Check it on `x^n`: `[z^(d−n)] (1+z)^(d−1−n)` is `1` when `n = d` and `0` otherwise.
Under `x = z/(1+z)`, `1 − x = (1+z)^(−1)` and `1 − 2x = (1−z)(1+z)^(−1)`, and since
`δ − 2 − f = δ − R − 1 + d`,

```
[x^d] (1−x)^(δ−R−1+d) (1−2x)^(−A) = [z^d] (1+z)^(A+R−δ) (1−z)^(−A)
                                  = Σ_k C(N,k) C(A+d−k−1, d−k),
```

which is B5-M7. ∎

## What the check does

| step | box | cases | mismatches |
|---|---|---|---|
| S1 indicator collapse, binary labels | `Q ≤ 5`, every `u`, `M`, `t ∈ E`, `B ⊆ active` | 689,730 | 0 |
| S1, ternary labels | `Q ≤ 3` | 23,766 | 0 |
| S2 inner sum, against the definition rewritten from scratch | `Q ≤ 5, A ≤ 3, R ≤ 4` | 380,464 | 0 |
| S3 closed form, against an exact rational solve written from scratch | `A ≤ 6, R ≤ 7` | 49 | 0 |
| S4 identity | `A ≤ 8, R ≤ 8, δ ≤ 12` | 3,132 | 0 |
| cross-check against the frozen source producer | `Q ≤ 5, A ≤ 3, R ≤ 4` | 380,464 | 0 |

Two mutated statements are required to fail, and they do:
- S1 with `t` left in `E`: 14,738 mismatches.
- B5-M7 with `N` off by one: 2,432 mismatches.

Steps S1–S4 import nothing from `reference-model/src`. Only the final,
separately labelled cross-check does.

## Standing

This is a written proof checked step by step on finite boxes. It is separately
written in this repository, not externally authored, so it does not discharge
external mathematical review. It does remove the dependence of the cost
theorem on a proof held only in the sealed archive.
