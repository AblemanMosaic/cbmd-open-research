"""Standalone residue/lift separation in the reference amplitude spectrum.

Standard library only; imports nothing from the archive. The amplitude is
recomputed here from the closed form

    n(A,R,delta,f) = 2^(R-1) * (-1)^A * sum_{k=0}^{d} C(N,k) * C(A+d-k-1, d-k),
    d = R-1-f,  N = A+R-delta,

with generalized binomials for negative upper index, and is independently
cross-checked against the defining Newton/parity construction so that the
closed form is not taken on trust.

Reported:
  1. the smallest class that vanishes modulo 3 while remaining nonzero over Z;
  2. the full residue/lift census at three native-like parameter triples;
  3. a recorded NEGATIVE: no bounded-depth low-digit criterion for v_3 exists
     off the central line, for depth t <= 3.
  4. adverse controls that must fail.
"""
from __future__ import annotations

import json
import sys
from fractions import Fraction
from math import comb as _comb


def comb(n: int, k: int) -> int:
    if k < 0 or (n >= 0 and k > n):
        return 0
    if n < 0:
        return (-1) ** k * _comb(-n + k - 1, k)
    return _comb(n, k)


# ---------- the amplitude, two independent ways ----------
def parity_coefficients_newton(A: int, R: int) -> list[int]:
    """Solve sum_j c_j C(A+i, j) = (-1)^(A+i) for i = 0..R-1 by exact elimination."""
    rows = [[Fraction(comb(A + i, j)) for j in range(R)] + [Fraction((-1) ** (A + i))]
            for i in range(R)]
    for j in range(R):
        p = next(i for i in range(j, R) if rows[i][j])
        rows[j], rows[p] = rows[p], rows[j]
        pivot = rows[j][j]
        rows[j] = [value / pivot for value in rows[j]]
        for i in range(R):
            if i != j:
                factor = rows[i][j]
                rows[i] = [a - factor * b for a, b in zip(rows[i], rows[j])]
    assert all(row[-1].denominator == 1 for row in rows), "parity vector must be integral"
    return [int(row[-1]) for row in rows]


def amplitude_defining(A: int, R: int, delta: int, f: int) -> int:
    """n from the parity vector: (-1)^f sum_{j>=f} c_j 2^(R-1-j) C(delta-1-f, j-f)."""
    c = parity_coefficients_newton(A, R)
    return (-1) ** f * sum(c[j] * 2 ** (R - 1 - j) * comb(delta - 1 - f, j - f)
                           for j in range(f, R))


def amplitude_closed(A: int, R: int, delta: int, f: int) -> int:
    d = R - 1 - f
    N = A + R - delta
    total = sum(comb(N, k) * (1 if d - k == 0 else comb(A + d - k - 1, d - k))
                for k in range(d + 1))
    return (-1) ** A * total * 2 ** (R - 1)


def v3(x: int) -> object:
    if x == 0:
        return "inf"
    x = abs(x)
    v = 0
    while x % 3 == 0:
        x //= 3
        v += 1
    return v


def carries3(a: int, b: int) -> int:
    carry = count = 0
    while a or b or carry:
        s = a % 3 + b % 3 + carry
        carry = 1 if s >= 3 else 0
        count += carry
        a //= 3
        b //= 3
    return count


def cross_check(max_A=6, max_R=6, span=10) -> dict:
    agree = disagree = 0
    first = None
    for A in range(max_A + 1):
        for R in range(1, max_R + 1):
            for f in range(R):
                for delta in range(f + 1, 2 * A + R + span):
                    a = amplitude_defining(A, R, delta, f)
                    b = amplitude_closed(A, R, delta, f)
                    if a == b:
                        agree += 1
                    else:
                        disagree += 1
                        first = first or {"A": A, "R": R, "delta": delta, "f": f,
                                          "defining": a, "closed": b}
    return {"agreements": agree, "disagreements": disagree, "first_disagreement": first}


def smallest_separation(limit=14, off_diagonal=False) -> dict | None:
    best = None
    for total in range(3, 4 * limit):
        for A in range(limit):
            for R in range(1, limit):
                for f in range(R):
                    for delta in range(f + 1, 3 * limit):
                        if A + R + delta != total:
                            continue
                        if off_diagonal and f >= delta - 1:
                            continue        # f = delta-1 is the diagonal column y = u
                        n = amplitude_closed(A, R, delta, f)
                        if n != 0 and n % 3 == 0:
                            cand = {"A": A, "R": R, "delta": delta, "f": f, "amplitude": n,
                                    "v3": v3(n), "zero_mod_3": True, "zero_over_Z": False,
                                    "A_plus_R_plus_delta": total}
                            if best is None:
                                best = cand
        if best is not None:
            return best
    return None


def census(triples) -> list:
    out = []
    for A, R, Q in triples:
        hist: dict[str, int] = {}
        residue_zero_lift_nonzero = 0
        exact_zero = 0
        for delta in range(2, Q + 1):
            for f in range(min(R, delta - 1)):
                n = amplitude_closed(A, R, delta, f)
                key = str(v3(n))
                hist[key] = hist.get(key, 0) + 1
                if n == 0:
                    exact_zero += 1
                elif n % 3 == 0:
                    residue_zero_lift_nonzero += 1
        out.append({"A": A, "R": R, "Q": Q, "v3_histogram": dict(sorted(hist.items())),
                    "residue_zero_lift_nonzero": residue_zero_lift_nonzero,
                    "exact_zero_over_Z": exact_zero,
                    "classes": sum(hist.values())})
    return out


def central_line_kummer(max_A=40, max_R=10) -> dict:
    """Positive control: on delta = 2A+R with even d, v_3 equals a carry count."""
    ok = bad = 0
    for A in range(1, max_A + 1):
        for R in range(1, max_R + 1):
            for f in range(R):
                d = R - 1 - f
                if d % 2:
                    continue
                n = amplitude_closed(A, R, 2 * A + R, f)
                if v3(n) == carries3(d // 2, A - 1):
                    ok += 1
                else:
                    bad += 1
    return {"instances": ok + bad, "agreements": ok, "disagreements": bad}


def low_digit_negative(depths=(2, 3), max_A=40, max_R=8, span=12) -> list:
    """Recorded NEGATIVE: v_3 off the central line is not a function of the low
    base-3 digits of A and N = A+R-delta together with d, at these depths."""
    rows = []
    for t in depths:
        M = 3 ** t
        table: dict[tuple, object] = {}
        conflicts = total = 0
        for A in range(1, max_A + 1):
            for R in range(1, max_R + 1):
                for f in range(R):
                    d = R - 1 - f
                    for delta in range(f + 1, 2 * A + R + span):
                        n = amplitude_closed(A, R, delta, f)
                        value = v3(n)
                        value = t if value == "inf" else min(value, t)
                        key = (A % M, (A + R - delta) % M, d)
                        total += 1
                        if key in table and table[key] != value:
                            conflicts += 1
                        table.setdefault(key, value)
        rows.append({"depth": t, "modulus": M, "points": total, "conflicting_points": conflicts,
                     "criterion_exists_at_this_depth": conflicts == 0})
    return rows


def main() -> int:
    report = {
        "schema": "cbmd.residue-lift-separation.v1",
        "closed_form_cross_check": cross_check(),
        "smallest_residue_zero_lift_nonzero": smallest_separation(),
        "smallest_off_diagonal_residue_zero_lift_nonzero": smallest_separation(off_diagonal=True),
        "native_like_census": census([(17, 5, 80), (15, 8, 80), (7, 4, 40)]),
        "central_line_kummer_control": central_line_kummer(),
        "recorded_negative_low_digit_criterion": low_digit_negative(),
        "nonclaims": [
            "the inherited selected-degree-six source fixture is NOT reproduced here; this file covers the amplitude spectrum only",
            "no native SAT consequence and no novelty determination",
            "a residue-zero class is not a lifted-zero class; that is the point of the separation",
        ],
        "authority_effect": "NONE",
    }
    checks = report["closed_form_cross_check"]
    ctrl = report["central_line_kummer_control"]
    sep = report["smallest_residue_zero_lift_nonzero"]
    negatives = report["recorded_negative_low_digit_criterion"]
    gates = []
    if checks["disagreements"] != 0:
        gates.append("closed form disagrees with the defining construction")
    if ctrl["disagreements"] != 0:
        gates.append("central-line Kummer control failed")
    if sep is None:
        gates.append("no residue/lift separation found (box is degenerate)")
    if report["smallest_off_diagonal_residue_zero_lift_nonzero"] is None:
        gates.append("no OFF-DIAGONAL residue/lift separation found; the diagonal case alone would be misleading")
    if not all(not row["criterion_exists_at_this_depth"] for row in negatives):
        gates.append("a low-digit criterion was NOT excluded; the recorded negative is wrong")
    if not any(row["residue_zero_lift_nonzero"] > 0 for row in report["native_like_census"]):
        gates.append("census found no residue/lift separation in native-like regimes")
    report["content_gate_failures"] = gates
    report["status"] = "PASS" if not gates else "FAIL"
    print(json.dumps(report, indent=1))
    return 0 if not gates else 1


if __name__ == "__main__":
    raise SystemExit(main())
