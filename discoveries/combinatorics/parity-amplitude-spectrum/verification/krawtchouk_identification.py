"""Which classical polynomial is this, exactly?

The dossier says the identification "reduces to classical Krawtchouk symmetry
and orthogonality".  A prior-art pass sharpened that in two ways, and this
script checks both rather than taking them on trust.

## The object, named

With the MacWilliams-Sloane binary Krawtchouk polynomial

    K_k(x; n) = sum_j (-1)^j C(x, j) C(n - x, k - j)

taken as a polynomial in an INDETERMINATE x, the reference amplitude is

    n(A, R, delta, f) = 2^(R-1) * (-1)^A * K_d(-A; R - delta),   d = R - 1 - f.

The matching is exact and, once written out, immediate: with the generalized
binomial `C(-A, j) = (-1)^j C(A+j-1, j)`, the sign cancels and the Krawtchouk
sum becomes `sum_j C(A+j-1, j) C(A+R-delta, d-j)`, which is the dossier's own
convolution.  So this is a naming observation, not a theorem -- but the name
is worth having right, because it says which classical facts are available.

## The correction

Orthogonality is **not** available.  Krawtchouk orthogonality sums over
i = 0..n with n a non-negative integer; here the argument is `x = -A`, which is
not in that range, and the length `n = R - delta` can itself be negative.  The
measure does not exist.  What survives is the generating function and the q=2
reflection symmetry, which are polynomial identities valid for arbitrary
exponents by the binomial series.  The dossier's phrase should drop
"and orthogonality", and this script checks that the symmetry it does rely on
holds while the orthogonality sum it cannot rely on is not even well posed.

## Centered vanishing, placed

On the centered line `delta = 2A + R`, the length is `n = R - delta = -2A` and
the argument is `x = -A`, which is exactly `n/2`.  The binary reflection law
`K_m(n - x) = (-1)^m K_m(x)` therefore forces `K_m(n/2) = 0` for odd `m`.  So
the dossier's centered vanishing is the classical statement that an odd-degree
binary Krawtchouk polynomial vanishes at the centre of its reflection
symmetry, not only a parity remark about an even power series.

Checked here: the identification, the reflection law, the centre coincidence,
and the even-degree values, each against the dossier's own amplitude.
"""
from __future__ import annotations

import json
from fractions import Fraction
from math import comb as _comb


def comb(n: int, k: int) -> int:
    if k < 0 or (n >= 0 and k > n):
        return 0
    if n < 0:
        return (-1) ** k * _comb(-n + k - 1, k)
    return _comb(n, k)


# ------------------------------------------------- the dossier's amplitude
def parity_coefficients(A: int, R: int) -> list[int]:
    """Solve sum_j c_j C(A+i, j) = (-1)^(A+i) for i = 0..R-1, exactly."""
    rows = [[Fraction(comb(A + i, j)) for j in range(R)] + [Fraction((-1) ** (A + i))]
            for i in range(R)]
    for j in range(R):
        p = next(i for i in range(j, R) if rows[i][j])
        rows[j], rows[p] = rows[p], rows[j]
        pivot = rows[j][j]
        rows[j] = [v / pivot for v in rows[j]]
        for i in range(R):
            if i != j:
                fac = rows[i][j]
                rows[i] = [a - fac * b for a, b in zip(rows[i], rows[j])]
    assert all(row[-1].denominator == 1 for row in rows)
    return [int(row[-1]) for row in rows]


def amplitude_defining(A: int, R: int, delta: int, f: int) -> int:
    c = parity_coefficients(A, R)
    return (-1) ** f * sum(c[j] * 2 ** (R - 1 - j) * comb(delta - 1 - f, j - f)
                           for j in range(f, R))


def amplitude_closed(A: int, R: int, delta: int, f: int) -> int:
    d = R - 1 - f
    N = A + R - delta
    total = sum(comb(N, k) * comb(A + d - k - 1, d - k) if d - k else comb(N, k)
                for k in range(d + 1))
    return (-1) ** A * total * 2 ** (R - 1)


# ------------------------------------------------- the classical polynomial
def krawtchouk(k: int, x: int, n: int) -> int:
    """K_k(x; n) for q = 2, MacWilliams-Sloane normalization, x an integer that
    need not lie in 0..n and n that need not be non-negative."""
    return sum((-1) ** j * comb(x, j) * comb(n - x, k - j) for j in range(k + 1))


def run(amax=7, rmax=8, dlo=-6, dhi=14):
    ident_checked = ident_bad = 0
    defining_checked = defining_bad = 0
    refl_checked = refl_bad = 0
    centre_checked = centre_bad = 0
    odd_zero = even_nonzero = 0
    samples = []

    for A in range(0, amax + 1):
        for R in range(1, rmax + 1):
            for delta in range(dlo, dhi + 1):
                for f in range(R):
                    d = R - 1 - f
                    n_amp = amplitude_closed(A, R, delta, f)
                    # (1) the identification
                    k = krawtchouk(d, -A, R - delta)
                    want = 2 ** (R - 1) * (-1) ** A * k
                    ident_checked += 1
                    if want != n_amp:
                        ident_bad += 1
                        if len(samples) < 4:
                            samples.append({"kind": "identification", "A": A, "R": R,
                                            "delta": delta, "f": f,
                                            "amplitude": n_amp, "krawtchouk_form": want})
                    # (2) the closed form against the defining construction
                    if R <= 6 and -4 <= delta <= 9:
                        defining_checked += 1
                        if amplitude_defining(A, R, delta, f) != n_amp:
                            defining_bad += 1
                    # (3) the binary reflection law K_m(n - x) = (-1)^m K_m(x)
                    nn = R - delta
                    refl_checked += 1
                    if krawtchouk(d, nn - (-A), nn) != (-1) ** d * k:
                        refl_bad += 1

    # (4) the centred line: argument is exactly n/2, odd degrees vanish,
    #     even degrees are the central coefficients
    for A in range(0, amax + 1):
        for R in range(1, rmax + 1):
            delta = 2 * A + R
            nn = R - delta
            if nn != -2 * A:
                centre_bad += 1
            for f in range(R):
                d = R - 1 - f
                centre_checked += 1
                n_amp = amplitude_closed(A, R, delta, f)
                if d % 2:
                    if n_amp != 0:
                        centre_bad += 1
                    else:
                        odd_zero += 1
                else:
                    e = d // 2
                    want = 2 ** (R - 1) * (-1) ** A * comb(A + e - 1, e)
                    if n_amp != want:
                        centre_bad += 1
                    elif n_amp != 0:
                        even_nonzero += 1

    gates = {
        "identification_exact": ident_bad == 0 and ident_checked > 0,
        "closed_form_matches_defining": defining_bad == 0 and defining_checked > 0,
        "reflection_law_holds": refl_bad == 0 and refl_checked > 0,
        "centred_line_as_stated": centre_bad == 0 and centre_checked > 0,
        "odd_degrees_actually_occur": odd_zero > 0,
        "even_degrees_actually_nonzero": even_nonzero > 0,
    }
    return {"schema": "cbmd.krawtchouk-identification.v1",
            "box": {"A_max": amax, "R_max": rmax, "delta": [dlo, dhi]},
            "identification": {"checked": ident_checked, "mismatches": ident_bad},
            "defining_vs_closed": {"checked": defining_checked,
                                   "mismatches": defining_bad},
            "reflection_law": {"checked": refl_checked, "mismatches": refl_bad},
            "centred_line": {"checked": centre_checked, "mismatches": centre_bad,
                             "odd_degrees_vanishing": odd_zero,
                             "even_degrees_nonzero": even_nonzero},
            "samples": samples,
            "gates": gates,
            "pass": all(gates.values()),
            "nonclaims": [
                "the identification is a naming observation: writing C(-A, j) with the "
                "generalized binomial turns the Krawtchouk sum into the dossier's own "
                "convolution, so nothing is proved by it",
                "orthogonality is NOT available at these parameters and is not checked; "
                "the argument lies outside 0..n and the length may be negative, so the "
                "measure does not exist",
                "the centred vanishing is a published root fact about binary Krawtchouk "
                "polynomials, not a result of this dossier",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    result = run()
    print(json.dumps(result, indent=1))
    raise SystemExit(0 if result["pass"] else 1)
