# Prior art

A bounded targeted search against the orthogonal-polynomial and coding-theory
literature, run to discharge the standing obligation for a prior-art
assessment. Its outcome is deflationary, which was the expected outcome, and
it corrects one piece of terminology that was doing real work.

## The object, named precisely

With the MacWilliams–Sloane binary Krawtchouk polynomial

```
K_k(x; n) = Σ_j (−1)^j C(x, j) C(n − x, k − j)
```

taken as a polynomial in an **indeterminate** `x`, the reference amplitude is

```
n(A, R, delta, f) = 2^(R−1) · (−1)^A · K_d(−A; R − delta),    d = R − 1 − f.
```

> N. J. A. Sloane, *An Introduction to Association Schemes and Coding Theory*,
> Eq. (17) and (20), the lecture-note form of MacWilliams & Sloane,
> *The Theory of Error-Correcting Codes*, Ch. 5.
> <https://math.mit.edu/~mqt/math/resources/sloane_intro-to-association-schemes-and-coding-theory.pdf>

Sloane states explicitly that `x` is an indeterminate and `K_k` a polynomial in
`x` of degree `k`, which is what licenses the negative argument here. Matching
exponents: `n − x = A + R − delta` and `x = −A`, hence `n = R − delta`.

The identification is verified in
[`verification/krawtchouk_identification.py`](../verification/krawtchouk_identification.py)
on 6,048 classes with no mismatch. It is worth saying plainly that this is a
**naming observation and not a theorem**: writing `C(−A, j) = (−1)^j C(A+j−1, j)`
cancels the sign and turns the Krawtchouk sum into the dossier's own
convolution in one line. The value of the name is that it says which classical
facts are available — and which are not.

## The correction: orthogonality is not available

The dossier's README said the identification *"reduces to classical Krawtchouk
symmetry and orthogonality"*. **Orthogonality is the wrong word here.**

Krawtchouk orthogonality is a sum over `i = 0 … n` against the binomial weight,
and it requires `n` to be a non-negative integer and the arguments to lie in
that range. Here the argument is `x = −A`, which is outside it, and the length
`n = R − delta` can itself be negative. The orthogonality measure does not
exist at these parameters, so nothing in this dossier can rest on it.

What does survive is the **generating function** and the **q = 2 reflection
symmetry**. Both are polynomial identities in the exponents, valid for
arbitrary values by the binomial series, and neither needs a measure. The
phrasing has been corrected to say symmetry only.

The nearest genuinely two-free-exponent family is **Meixner**, not
"negative-parameter Krawtchouk": DLMF 18.23.4 gives the Meixner generating
function `(1 − z/c)^x (1 − z)^(−x−β)`, with Krawtchouk the degenerate point
`c = −1` for `p = 1/2`. <https://dlmf.nist.gov/18.23>

Work extending discrete classical families beyond orthogonality exists —
Costas-Santos and Sánchez-Lara, *Extensions of discrete classical orthogonal
polynomials beyond the orthogonality*, <https://arxiv.org/pdf/0710.4930> —
but it treats Meixner with `c < 0` and complex `β` and explicitly excludes
`−β ∈ ℕ`, which is exactly the Krawtchouk case. Nothing from that line is
needed, because the generating-function identity requires no analytic
continuation at all.

Jacobi is a worse fit, not a better one. The coefficient does equal
`2^d · P_d^(a−d, b−d)(0)`, but the parameters then depend on the degree.

## Centered vanishing is a published root fact

The dossier's centered vanishing — on `delta = 2A + R`, the amplitude vanishes
for odd `d` — reads naturally as a parity remark: the generating function
becomes `(1 − y²)^(−A)`, which is even. That reading is correct and the
statement is also classical under its proper name.

> R. Coleman, *On Krawtchouk polynomials*, arXiv:1101.1798 (2011), Lemma 5.1
> and Proposition 5.2. <https://ar5iv.labs.arxiv.org/html/1101.1798>

For `q = 2`, `K_m(n − x) = (−1)^m K_m(x)`, so `n/2` is a root whenever `m` is
odd. On the centered line, `n = R − delta = −2A` and `x = −A`, which is `n/2`
**exactly**. So the centered vanishing is the statement that an odd-degree
binary Krawtchouk polynomial vanishes at the centre of its own reflection
symmetry. The even values `C(A + e − 1, e)` are the equally classical central
coefficients. The reflection law and the centre coincidence are both checked in
the verifier.

## The coefficient-extraction form

The step from the linear system — interpolate `(−1)^(A+i)` in the basis
`C(A+i, j)`, then weight by `2^(R−1−j) C(delta−1−f, j−f)` and resum — is
Newton forward-difference interpolation followed by Vandermonde–Chu
convolution. The solved vector is `c_j = Δ^j P(0)` for the interpolant `P`;
for `A = 0` it is exactly `(−2)^j`. The resummation is the binomial-transform
dictionary, the substitution `y ↦ y/(1−y)`. Standard finite-difference
calculus; DLMF §18.23 and Graham–Knuth–Patashnik Ch. 5 cover both halves. No
named theorem attaches to the particular assembly, which is bookkeeping over
two textbook identities.

## Verdicts

| claim | verdict |
|---|---|
| coefficient-extraction form | textbook: Newton interpolation plus Vandermonde |
| Krawtchouk identification | classical, and now named precisely; the word *orthogonality* withdrawn |
| centered vanishing | textbook, and a published root fact rather than only a parity remark |

Nothing in this dossier is claimed as new on the strength of this search. What
it adds is precision about which classical object is in play, and the removal
of an availability claim — orthogonality — that the parameters do not support.

## Still owed

An independent **source-specific** derivation and convention audit. This search
settled the mathematics' provenance, not the question of whether the reference
amplitude is correctly read off the source conventions, which needs the
archive.
