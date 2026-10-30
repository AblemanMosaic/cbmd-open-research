"""A base-three digit criterion off the central line, and what the recorded
negative was actually about.

`separation.py` records a NEGATIVE: off the central line `delta = 2A + R`, the
valuation `v_3` is not a function of the low base-three digits of `A` and
`N = A + R - delta` together with `d`, at depth 2 or 3.  That rules out a fixed
WINDOW of digits read without state.  It does not rule out a digit criterion
that carries state, and the open obligation was to settle whether one exists.

One does, for the vanishing predicate, and it is small.

## The reduction

Dropping the 3-adic unit `2^(R-1)`,

    alpha(A,R,delta,f) = (-1)^A [y^d] (1+y)^N (1-y)^(-A),
    d = R-1-f,   N = A+R-delta.

Over `F_3`, `(1 +- y)^(3^m) = 1 +- y^(3^m)`, so a series agrees up to degree
`d` with the one whose exponent is reduced mod `3^m` whenever `3^m > d`.  With
`M = N mod 3^m` and `B = (-A) mod 3^m`,

    alpha = (-1)^A [y^d] (1+y)^M (1-y)^B   (mod 3).

Those exponents are the **3-adic** digit expansions of `N` and `-A`, which are
eventually all twos when the integer is negative; that is the sense in which
this is a digit criterion, and the reason a window of low digits of `A` and `N`
could never have sufficed.

## The automaton

Lucas factors both: `(1+y)^M = prod_i (1 + y^(3^i))^(M_i)`.  Position `i`
contributes `a_i` copies of `3^i` from the first product and `b_i` from the
second, with `0 <= a_i <= M_i` and `0 <= b_i <= B_i`, so `a_i + b_i <= 4` and
matching the digits of `d` needs a carry in `{0, 1}`.  Reading the digit
triples `(M_i, B_i, d_i)` least significant first, with that carry as the whole
state and the sign `(-1)^(b_i)` folded into the weight, is a two-state
automaton computing `alpha mod 3`.

## What is checked

  * the automaton against the amplitude, over the stated box, with both
    outcomes required to occur;
  * the same automaton with the carry deleted, which must FAIL -- otherwise
    the carry is not what the recorded negative was missing;
  * independence of the modulus `3^m`, so the reduction is not an artifact of
    one choice;
  * agreement with the DEFINING Newton construction, not only the closed form,
    on a sample.

## What is NOT claimed

The valuation itself is not shown to be digit-computable.  `v_3` is unbounded,
so it is not an automatic function with a finite output alphabet; whether it is
3-regular in the transducer sense is left open.  The criterion here is for the
residue, which is what a transported zero certificate actually depends on.
"""
from __future__ import annotations

import json
import os
import sys
from math import comb as _comb

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from separation import amplitude_closed, amplitude_defining, v3


def digits3(n: int, length: int) -> list[int]:
    return [(n // 3 ** i) % 3 for i in range(length)]


def modulus_exponent(A: int, d: int, N: int) -> int:
    m = 1
    while 3 ** m <= max(d, A, abs(N)):
        m += 1
    return m


def automaton_mod3(A: int, R: int, delta: int, f: int,
                   m: int | None = None, no_carry: bool = False) -> int:
    """alpha * 2^(R-1) mod 3, by the two-state digit automaton."""
    d = R - 1 - f
    if d < 0:
        return 0
    N = A + R - delta
    if m is None:
        m = modulus_exponent(A, d, N)
    mod = 3 ** m
    dm = digits3(N % mod, m)
    bm = digits3((-A) % mod, m)
    dd = digits3(d, m)
    state = {0: 1}
    for i in range(m):
        nxt: dict[int, int] = {}
        for carry, acc in state.items():
            for a in range(dm[i] + 1):
                ca = _comb(dm[i], a) % 3
                if ca == 0:
                    continue
                for b in range(bm[i] + 1):
                    cb = (_comb(bm[i], b) * (-1) ** b) % 3
                    if cb == 0:
                        continue
                    total = a + b + (0 if no_carry else carry)
                    if total % 3 != dd[i]:
                        continue
                    out = 0 if no_carry else total // 3
                    nxt[out] = (nxt.get(out, 0) + acc * ca * cb) % 3
        state = nxt
        if not state:
            break
    value = (state.get(0, 0) * (-1) ** A) % 3 if state else 0
    return (value * pow(2, R - 1, 3)) % 3


def run(amax=25, rmax=14, dmax=30, defining_sample=240):
    checked = agree = disagree = 0
    zero3 = nonzero3 = 0
    nocarry_wrong = 0
    modulus_mismatch = 0
    defining_checked = defining_bad = 0
    vmax = 0
    samples = []
    for A in range(0, amax + 1):
        for R in range(1, rmax + 1):
            for delta in range(0, dmax + 1):
                for f in range(R):
                    n = amplitude_closed(A, R, delta, f)
                    want = n % 3
                    got = automaton_mod3(A, R, delta, f)
                    checked += 1
                    if want == 0:
                        zero3 += 1
                    else:
                        nonzero3 += 1
                    if want == got:
                        agree += 1
                    else:
                        disagree += 1
                        if len(samples) < 5:
                            samples.append({"A": A, "R": R, "delta": delta,
                                            "f": f, "n": n,
                                            "want": want, "got": got})
                    if automaton_mod3(A, R, delta, f, no_carry=True) != want:
                        nocarry_wrong += 1
                    # the reduction must not depend on which 3^m is chosen
                    m0 = modulus_exponent(A, R - 1 - f, A + R - delta)
                    if automaton_mod3(A, R, delta, f, m=m0 + 2) != got:
                        modulus_mismatch += 1
                    val = v3(n)
                    if val != "inf":
                        vmax = max(vmax, val)
                    if defining_checked < defining_sample and R <= 6 and delta <= 8:
                        defining_checked += 1
                        if amplitude_defining(A, R, delta, f) != n:
                            defining_bad += 1

    gates = {
        "automaton_is_exact": disagree == 0,
        "both_residues_occur": zero3 > 0 and nonzero3 > 0,
        "carry_is_load_bearing": nocarry_wrong > 0,
        "independent_of_the_modulus": modulus_mismatch == 0,
        "closed_form_matches_the_defining_construction":
            defining_bad == 0 and defining_checked > 0,
    }
    return {"schema": "cbmd.residue-digit-criterion.v1",
            "box": {"A_max": amax, "R_max": rmax, "delta_max": dmax},
            "checked": checked,
            "agreements": agree,
            "DISAGREEMENTS": disagree,
            "zero_mod_3": zero3,
            "nonzero_mod_3": nonzero3,
            "carryless_automaton_wrong_on": nocarry_wrong,
            "modulus_mismatches": modulus_mismatch,
            "defining_construction_checked": defining_checked,
            "defining_construction_disagreements": defining_bad,
            "largest_v3_observed": vmax,
            "samples": samples,
            "gates": gates,
            "pass": all(gates.values()),
            "nonclaims": [
                "the criterion is for the residue mod 3, not for the valuation; "
                "v_3 is unbounded and so is not an automatic function with a finite "
                "output alphabet, and its 3-regularity is left open",
                "a finite census over the stated box; the reduction is argued in prose "
                "and is not compiled",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    result = run()
    print(json.dumps(result, indent=1))
    raise SystemExit(0 if result["pass"] else 1)
