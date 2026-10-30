# The residue/lift separation, extracted

## What this file adds

The discovery's standing obligation was to "publish the smallest neutral
source-bound fixture with its exact ring arithmetic, then replay it
independently at residue and lifted precisions." This extracts the
**amplitude-spectrum half** of that obligation as a standalone artifact. The
inherited selected-degree-six source fixture is *not* reproduced here and
remains outstanding.

## The amplitude

For the reference amplitude family, with `d = R-1-f` and `N = A+R-delta`,

```
n(A,R,delta,f) = 2^(R-1) (-1)^A sum_{k=0}^{d} C(N,k) C(A+d-k-1, d-k)
```

with generalized binomials for negative upper index. `verification/separation.py`
recomputes this from the defining Newton/parity construction and checks the two
agree on 2,597 instances, so the closed form is not taken on trust.

## Smallest separation

The smallest class vanishing modulo three while nonzero over the integers, among
genuinely off-diagonal columns (`f < delta - 1`), is

```
A = 0, R = 2, delta = 5, f = 0.
parity vector c = (1, -2);  n = 1*2*C(4,0) + (-2)*1*C(4,1) = 2 - 8 = -6.
v_3(-6) = 1:  zero in Z/3, nonzero in Z and in Z/9.
```

Four integers and two binomials. A residue-level activity test calls this row
inactive; it is not. Including the diagonal column `f = delta - 1` the smallest
is `A=1, R=2, delta=1, f=0`, also `-6`, but a diagonal column is nonzero for a
separate reason and makes a poor headline witness.

## Census at native-like parameters

| `(A,R,Q)` | classes | `v_3 = 0` | zero mod 3, nonzero over Z | zero over Z |
|---|---|---|---|---|
| (17,5,80) | 385 | 263 | **120** | 2 |
| (15,8,80) | 604 | 331 | **269** | 4 |
| (7,4,40) | 150 | 124 | **24** | 2 |

Roughly a third of the classes in the first regime are residue-zero; fewer than
one percent are genuinely zero. Any procedure that treats "vanishes mod 3" as
"vanishes" is wrong on 120 of 385 classes at `(17,5,80)`.

## Positive control and a recorded negative

**Control.** On the central line `delta = 2A+R` with even `d`, `v_3` of the
amplitude equals the number of carries when adding `d/2` and `A-1` in base three
(Kummer). Verified on 1,200 instances, no exceptions. This shows the valuation
is not arbitrary where the amplitude is a single binomial.

**Negative.** Off the central line it is **not** a function of the low base-three
digits. Treating `v_3` truncated at depth `t` as a function of
`(A mod 3^t, N mod 3^t, d)` produces 3,967 conflicting points at `t = 2` and
1,144 at `t = 3`, over 79,680 points. No bounded-depth low-digit criterion
exists at these depths. A full-digit criterion is neither found nor excluded.

This negative is recorded as research output. It closes a route rather than
opening one, and it is the reason no general valuation criterion is claimed.

## Nonclaims

The inherited degree-six source fixture is not reproduced here; no native SAT
consequence; no novelty determination. A residue-zero class is not a lifted-zero
class, which is the entire point.

## A digit criterion for the residue (revision 0.3.0)

The recorded negative above rules out a fixed window of low base-three digits
for `v_3`. It does not rule out a digit criterion with state, and for the
residue one exists.

Drop the 3-adic unit `2^(R-1)` and write the amplitude as

```
alpha(A, R, delta, f) = (-1)^A [y^d] (1+y)^N (1-y)^(-A),
d = R - 1 - f,   N = A + R - delta.
```

Over `F_3`, `(1 ± y)^(3^m) = 1 ± y^(3^m)`, so for any `3^m > d` the series
agrees up to degree `d` with the one whose exponent is reduced modulo `3^m`:

```
alpha ≡ (-1)^A [y^d] (1+y)^M (1-y)^B   (mod 3),
M = N mod 3^m,   B = (-A) mod 3^m.
```

`M` and `B` are the **three-adic** expansions of `N` and `-A`, eventually all
twos when the integer is negative. That is the first reason a window on the
low digits of `A` and `N` as integers could not work: it was reading the wrong
digit string.

Lucas factors both exponents, so position `i` contributes `a_i` copies of
`3^i` from the first product and `b_i` from the second, with `0 ≤ a_i ≤ M_i`
and `0 ≤ b_i ≤ B_i`. Since `a_i + b_i ≤ 4`, matching the digits of `d` requires
a carry in `{0, 1}`. Reading the digit triples `(M_i, B_i, d_i)` least
significant first, with the carry as the whole state and the sign `(-1)^(b_i)`
folded into the weight, computes `alpha mod 3` in two states. That is the
second reason: a window reads digits in isolation, and this criterion needs
information to propagate upward.

Checked on 84,630 classes with no disagreement, with the carry shown to be
load-bearing (28,195 wrong without it), with the exponent reduction controlled
across two moduli, and with the closed form re-checked against the defining
construction.

The valuation is a different matter. `v_3` is unbounded — it reaches 10 inside
the measured box — so it is not an automatic function with a finite output
alphabet. Whether it is 3-regular in the transducer sense, as the carry count
is on the central line, is open.
