"""Labeled chip-firing on Z with an odd number of chips: small exact checks (pure Python).

Model (Hopkins-McConville-Propp, Sorting via chip-firing, EJC 24(3) 2017): n labeled
chips at 0; a site with at least two chips fires a chosen pair, the smaller chip
to the left neighbour and the larger to the right. For n = 2m + 1 every stable
outcome has one chip on each of -m..m.

Gates (each required):
  * INVERSIONS_n_le_9: the maximal inversion number of a stable outcome is m
    for n = 3, 5, 7, 9 (HMP Conjecture 26, which they verified for n <= 9);
  * EXACT_PROBABILITIES_n_le_9: under protocols 1 and 2, P(sorted) for
    n = 3, 5, 7 equals 1/3, 1/5 and the recorded values (exact rationals),
    and for n = 9 matches the recorded floating value;
  * The n = 11 values (max inversions 5; P(sorted) = 0.3305156511 and
    0.3314399523) come from the C++ tools and are recorded in evidence.
"""
from __future__ import annotations
import json
from fractions import Fraction


def outcomes(n):
    start = tuple([0] * n)
    seen = {start}
    stack = [start]
    finals = set()
    while stack:
        s = stack.pop()
        at = {}
        for i, p in enumerate(s):
            at.setdefault(p, []).append(i)
        moved = False
        for p, v in at.items():
            if len(v) >= 2:
                moved = True
                for a in range(len(v)):
                    for b in range(a + 1, len(v)):
                        t = list(s)
                        t[v[a]] = p - 1
                        t[v[b]] = p + 1
                        t = tuple(t)
                        if t not in seen:
                            seen.add(t)
                            stack.append(t)
        if not moved:
            finals.add(tuple(i + 1 for _, i in sorted((p, i) for i, p in enumerate(s))))
    return finals


def inversions(p):
    return sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j])


def p_sorted(n, proto):
    cur = {tuple([0] * n): Fraction(1)}
    ps = Fraction(0)
    while cur:
        nxt = {}
        for s, pr in cur.items():
            at = {}
            for i, p in enumerate(s):
                at.setdefault(p, []).append(i)
            U = [q for q, v in at.items() if len(v) >= 2]
            if not U:
                if all(s[i] == i - (n - 1) // 2 for i in range(n)):
                    ps += pr
                continue
            tot = sum(len(at[q]) * (len(at[q]) - 1) // 2 for q in U)
            for q in U:
                v = at[q]
                pairs = len(v) * (len(v) - 1) // 2
                w = pr / len(U) / pairs if proto == 2 else pr / tot
                for a in range(len(v)):
                    for b in range(a + 1, len(v)):
                        t = list(s)
                        t[v[a]] = q - 1
                        t[v[b]] = q + 1
                        t = tuple(t)
                        nxt[t] = nxt.get(t, 0) + w
        cur = nxt
    return ps


def main():
    inv_ok = all(max(inversions(p) for p in outcomes(n)) == (n - 1) // 2 for n in (3, 5, 7, 9))
    probs = {}
    for proto in (1, 2):
        for n in (3, 5, 7, 9):
            probs[f"proto{proto}_n{n}"] = p_sorted(n, proto)
    ok = (probs["proto2_n3"] == Fraction(1, 3) and probs["proto2_n5"] == Fraction(1, 5)
          and abs(float(probs["proto2_n7"]) - 0.2500960288) < 1e-9 and abs(float(probs["proto2_n9"]) - 0.3118227478) < 1e-9
          and abs(float(probs["proto1_n7"]) - 0.2511956417) < 1e-9 and abs(float(probs["proto1_n9"]) - 0.3146777496) < 1e-9)
    out = {"schema": "cbmd.labeled-chip-firing-line.v1",
           "exact_probabilities": {k: [str(v), float(v)] for k, v in probs.items()},
           "gates": {"INVERSIONS_n_le_9": inv_ok, "EXACT_PROBABILITIES_n_le_9": ok},
           "authority_effect": "NONE"}
    out["status"] = "PASS" if all(out["gates"].values()) else "FAIL"
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
