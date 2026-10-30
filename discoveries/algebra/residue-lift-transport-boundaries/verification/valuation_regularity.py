"""The valuation question, reduced to a polynomial and then settled by a
published theorem.

Revision 0.3.0 left this open: is `v_3` of the amplitude, off the central line,
3-regular in the transducer sense?  Two steps answer it, and the second is not
ours.

## Step one: the amplitude is a polynomial

For fixed `(A, R, f)`,

    alpha = (-1)^A sum_{k=0}^{d} C(N,k) C(A+d-k-1, d-k),   d = R-1-f,

and `N = A + R - delta` appears only in `C(N,k)`, a polynomial in `N` of degree
`k`.  So `alpha` is an integer-valued polynomial in `N` of degree exactly `d`,
the leading term coming from `k = d` with coefficient `1/d!`.  The question is
therefore the 3-adic valuation of the values of a fixed polynomial.

## Step two: that question has a published answer

> Zhang Shu and Jia-Yan Yao, *Analytic functions over Z_p and p-regular
> sequences*, C. R. Acad. Sci. Paris 349 (2011) 947-952,
> <https://www.numdam.org/item/CRMATH_2011__349_17-18_947_0/>
>
> Bartosz Sobolewski, *On k-regularity of sequences of valuations and last
> nonzero digits*, Ramanujan J. 61 (2023) 1151-1195,
> <https://arxiv.org/pdf/2202.09922> (Theorem 2.3, Remark 2.2)

For analytic `f` on `Z_p` with root set `R_f` inside `Z_p`, the sequence
`v_p(f(n))` is **periodic** if `R_f` is empty, **p-regular** if `R_f` is
non-empty and contained in `Q`, and **not regular** if `R_f` contains an
irrational.  Sobolewski's version allows roots in `N`.

So: `v_3` of the amplitude is 3-regular for a family exactly when every root of
that family's polynomial lying in `Z_3` is rational -- and for the families
that acquire an irrational 3-adic root it is **not** regular.  The answer to
0.3.0's question is no in general, and the criterion is sharp.

## What this script checks

The theorem is cited, not reproved.  What is checked is that it applies and
that the reduction is right:

  * the amplitude really is a polynomial in `N`: interpolate through `d+1`
    points and test far outside the interpolation range;
  * each family is classified by its root set in `Z_3`, exactly -- rational
    roots by the rational root theorem on the cleared-denominator integer
    polynomial, roots in `Z_3` by Hensel lifting;
  * the measured 3-kernel rank behaves as the trichotomy says: stabilizing
    when `R_f` is empty or rational, climbing when it contains an irrational;
  * controls on plain polynomials whose root structure is known by
    construction, including one case per branch of the trichotomy.

A truncated window can only LOWER an observed rank, so a rank that keeps
climbing is evidence the module is genuinely larger, while a rank that stops
climbing is not proof that it stops.  The controls are what make the test
readable in both directions.
"""
from __future__ import annotations

import json
import os
import sys
from fractions import Fraction
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from separation import amplitude_closed


def v3int(x: int):
    if x == 0:
        return None
    x = abs(x)
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v


def rank(rows) -> int:
    rows = [[Fraction(x) for x in r] for r in rows]
    r = 0
    cols = len(rows[0]) if rows else 0
    for c in range(cols):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                fac = rows[i][c]
                rows[i] = [a - fac * b for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


# ------------------------------------------------------- the polynomial
def integer_poly(A: int, R: int, f: int):
    """Coefficients of an integer multiple of the amplitude polynomial in N,
    lowest degree first, together with the clearing factor."""
    d = R - 1 - f
    pts = [(Fraction(n), Fraction(amplitude_closed(A, R, A + R - n, f)))
           for n in range(d + 1)]
    coeffs = [Fraction(0)] * (d + 1)
    for i, (xi, yi) in enumerate(pts):
        basis = [Fraction(1)]
        denom = Fraction(1)
        for j, (xj, _) in enumerate(pts):
            if i == j:
                continue
            denom *= (xi - xj)
            new = [Fraction(0)] * (len(basis) + 1)
            for k, c in enumerate(basis):
                new[k] -= c * xj
                new[k + 1] += c
            basis = new
        for k, c in enumerate(basis):
            coeffs[k] += yi * c / denom
    lcm = 1
    for c in coeffs:
        lcm = lcm * c.denominator // gcd(lcm, c.denominator)
    return [int(c * lcm) for c in coeffs], lcm


def polynomial_agrees(A, R, f, lo=-15, hi=30) -> bool:
    coeffs, lcm = integer_poly(A, R, f)
    for N in range(lo, hi):
        got = sum(c * N ** i for i, c in enumerate(coeffs))
        if got != lcm * amplitude_closed(A, R, A + R - N, f):
            return False
    return True


# ------------------------------------------------------- the root set
def rational_roots(coeffs):
    nz = [i for i, c in enumerate(coeffs) if c]
    if not nz:
        return None
    low, high = nz[0], nz[-1]
    a0, an = coeffs[low], coeffs[high]

    def divisors(m):
        m = abs(m)
        return [k for k in range(1, m + 1) if m % k == 0]

    roots = {Fraction(0)} if low > 0 else set()
    for p_ in divisors(a0):
        for q_ in divisors(an):
            for s in (1, -1):
                r = Fraction(s * p_, q_)
                if sum(Fraction(c) * r ** i for i, c in enumerate(coeffs)) == 0:
                    roots.add(r)
    return sorted(roots)


def z3_survivors(coeffs, depth=30):
    cur = [r for r in range(3)
           if sum(c * r ** i for i, c in enumerate(coeffs)) % 3 == 0]
    mod = 3
    for _ in range(depth - 1):
        nxt = []
        for r in cur:
            for t in range(3):
                cand = r + t * mod
                if sum(c * cand ** i for i, c in enumerate(coeffs)) % (mod * 3) == 0:
                    nxt.append(cand)
        cur = nxt
        mod *= 3
        if not cur:
            break
    return cur, mod


def deflate(coeffs, r: Fraction):
    """Divide the polynomial by (x - r), assuming r is a root."""
    co = [Fraction(c) for c in coeffs]
    n = len(co) - 1
    out = [Fraction(0)] * n
    carry = Fraction(0)
    for i in range(n, 0, -1):
        carry = co[i] + carry * r if i < n else co[i]
        out[i - 1] = carry
    return out


def strip_rational_roots(coeffs):
    """Remove every rational root, with multiplicity.  Testing for roots in Z_3
    by Hensel survivors is only reliable once these are gone: two rational roots
    three apart make the product divisible by 9 at every lift, so survivors
    persist with no further root behind them.  An earlier draft skipped this and
    duly misclassified (x+2)(x-1)."""
    co = [Fraction(c) for c in coeffs]
    found = []
    changed = True
    while changed and len(co) > 1:
        changed = False
        ints = [int(c * _clear(co)) for c in co]
        rs = rational_roots(ints) or []
        for r in rs:
            if sum(c * r ** i for i, c in enumerate(co)) == 0:
                co = deflate(co, r)
                found.append(r)
                changed = True
                break
    return [int(c * _clear(co)) for c in co], found


def _clear(co):
    lcm = 1
    for c in co:
        lcm = lcm * c.denominator // gcd(lcm, c.denominator)
    return lcm


def branch(coeffs, depth=30) -> str:
    """Which branch of the Shu-Yao / Sobolewski trichotomy this polynomial is in.

    Rational roots are removed first; what survives Hensel lifting afterwards is
    a genuine root of Z_3 by compactness, and it cannot be rational."""
    rest, rational = strip_rational_roots(coeffs)
    surv, _mod = z3_survivors(rest, depth=depth) if len(rest) > 1 else ([], 3)
    if surv:
        return "irrational_root"
    in_z3 = [r for r in rational if r.denominator % 3 != 0]
    return "rational_roots" if in_z3 else "empty_root_set"


# ------------------------------------------------------- the rank measurement
def kernel_ranks_poly(coeffs, depth=6, window=80, offset=0):
    length = window * 3 ** depth
    s = []
    for n in range(offset, offset + length):
        val = sum(c * n ** i for i, c in enumerate(coeffs))
        got = v3int(val)
        if got is None:
            return None
        s.append(got)
    rows, out = [], []
    for k in range(depth + 1):
        for r in range(3 ** k):
            rows.append([s[3 ** k * n + r] for n in range(window)])
        out.append(rank(rows))
    return out


def measure(coeffs, depth=6, window=80):
    for offset in (0, 1, 2, 5, 11, 29):
        rk = kernel_ranks_poly(coeffs, depth=depth, window=window, offset=offset)
        if rk is not None:
            return rk, offset
    return None, None


# ------------------------------------------------------- controls and census
CONTROLS = [
    ("x+1", [1, 1]),
    ("3x+1", [1, 3]),
    ("x^2-7", [-7, 0, 1]),
    ("x^2+3x-3", [-3, 3, 1]),
    ("x^3-x-3", [-3, -1, 0, 1]),
    ("x^2+x-2", [-2, 1, 1]),
    ("x^2-3x+2", [2, -3, 1]),
]

FAMILIES = ((1, 2, 0), (1, 3, 1), (1, 4, 2), (1, 4, 0), (1, 5, 0), (1, 5, 1),
            (1, 6, 0), (2, 4, 1), (2, 5, 0), (3, 5, 2))


def expect_stable(b: str) -> bool:
    return b in ("empty_root_set", "rational_roots")


def run():
    control_rows, control_bad = [], 0
    for name, coeffs in CONTROLS:
        b = branch(coeffs)
        rk, off = measure(coeffs)
        if rk is None:
            control_rows.append({"poly": name, "skipped": "vanishes at every offset"})
            continue
        stable = rk[-1] == rk[-2] == rk[-3]
        ok = stable == expect_stable(b)
        control_bad += (not ok)
        control_rows.append({"poly": name, "branch": b, "ranks": rk,
                             "offset": off, "stabilized": stable,
                             "as_the_theorem_says": ok})

    fam_rows, fam_bad, poly_bad = [], 0, 0
    for (A, R, f) in FAMILIES:
        coeffs, lcm = integer_poly(A, R, f)
        is_poly = polynomial_agrees(A, R, f)
        poly_bad += (not is_poly)
        b = branch(coeffs)
        rk, off = measure(coeffs)
        row = {"A": A, "R": R, "f": f, "degree": R - 1 - f,
               "is_polynomial_in_N": is_poly,
               "integer_poly": coeffs, "scaled_by": lcm, "branch": b}
        if rk is None:
            row["skipped"] = "vanishes at every offset"
        else:
            stable = rk[-1] == rk[-2] == rk[-3]
            ok = stable == expect_stable(b)
            fam_bad += (not ok)
            row.update({"ranks": rk, "offset": off, "stabilized": stable,
                        "as_the_theorem_says": ok})
        fam_rows.append(row)

    branches_seen = {r["branch"] for r in control_rows if "branch" in r}
    gates = {
        "amplitude_is_polynomial_in_N": poly_bad == 0,
        "controls_match_the_theorem": control_bad == 0,
        "families_match_the_theorem": fam_bad == 0,
        "every_branch_exercised_by_a_control": branches_seen >= {
            "empty_root_set", "rational_roots", "irrational_root"},
        "both_rank_behaviours_seen_in_families":
            len({r.get("stabilized") for r in fam_rows if "ranks" in r}) == 2,
    }
    return {"schema": "cbmd.valuation-regularity.v1",
            "theorem": ("Shu and Yao 2011; Sobolewski 2023 Theorem 2.3: for analytic f "
                        "on Z_p, v_p(f(n)) is periodic if f has no root in Z_p, "
                        "p-regular if its roots in Z_p are all rational, and not regular "
                        "if some root in Z_p is irrational"),
            "controls": control_rows,
            "families": fam_rows,
            "gates": gates,
            "pass": all(gates.values()),
            "nonclaims": [
                "the trichotomy is a published theorem and is cited, not reproved here",
                "the rank measurement is evidence, not proof: a truncated window can only "
                "lower an observed rank, so climbing is informative and stabilizing is not "
                "conclusive on its own",
                "the reduction of the amplitude to a polynomial in N is elementary and is "
                "checked by interpolation, not compiled",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    result = run()
    print(json.dumps(result, indent=1))
    raise SystemExit(0 if result["pass"] else 1)
