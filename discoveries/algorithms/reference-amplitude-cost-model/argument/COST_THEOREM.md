# B5 cost theorem: computing the source amplitude (r5)

Scope: the **reference producer** `src/owner_sum.py::literal_numerator` (enumeration route) versus the master formula B5-M7 (closed route), both computing the same integer `n(A,R,|D|,|E|−1)`. All counts are exact; the cost model is declared; the native claim is excluded in §5. Evidence: `evidence/pb/cost_theorem.py`, `evidence/pb/cost_theorem.json`.

## 1. Cost model BCM-1 (declared, not derived)

- Integers carry their bit length `bits(x)`. A multiplication or exact division of `x` by `y` costs `bits(x)·bits(y)` bit-operations (schoolbook); an addition costs `max(bits(x),bits(y))`.
- An indicator test `[swap(base,B) = y]` costs `Q` coordinate comparisons; forming `swap(base,B)` costs `Q` writes.
- No memoisation across amplitudes (the frozen producer has none). The parity vector solve is charged separately.
- Not charged: Python interpreter overhead, allocation, list construction. Wall-clock is reported as a diagnostic only and is part of no claim.

## 2. Enumeration route: exact count (B5-K2)

**Theorem 2.1.** For every `(u, y, t)` with `y` in the orbit and `t ∈ E(y)`, `literal_numerator(u,y,t,A,R)` performs exactly
`T_enum(Q,R) = Σ_{j=0}^{R−1} C(Q−1, j) · 2^j`
indicator tests, each on a length-`2Q` tuple, plus one `parity(A,R)` solve (`≥ R(R+1)` rational cells).
*Proof.* The loops enumerate every `S ⊆ [Q]∖{t}` with `|S| = j < R` and every `B ⊆ S`, with no early exit; `Σ_{B⊆S} 1 = 2^j`. ∎
Checked: the producer's own meter `numerator_delta_terms` equals `T_enum(Q,R)` on 163,912 calls, 0 exceptions.

Values: `T_enum(80,5) = 24,685,131`; `T_enum(80,8) = 389,575,972,971`; `T_enum(40,4) = 76,155`. Since every test is independent of the result and the loop has no exit, this is a lower bound on any execution of this producer, not only a measurement.

## 3. Closed route: upper bound (B5-K1)

Write `d = R−1−f`, `N = A+R−|D|`. By B5-M7,
`n = 2^{R−1} · (−1)^A · Σ_{k=0}^{d} C(N,k) · C(A+d−k−1, d−k)`.

**Algorithm.** Compute `g_i = C(A+i−1, i)` for `i = 0..d` incrementally (`g_i = g_{i−1}(A+i−1)/i`), `C(N,k)` incrementally in `k` (valid for negative `N` as generalised binomials), accumulate the `d+1` products, multiply by `2^{R−1}`.

**Theorem 3.1.** Under BCM-1 the closed route uses at most `3d+2 ≤ 3R−1` multiplications, `2d ≤ 2R−2` exact divisions and `d+1 ≤ R` additions, on integers of at most `O(R · log₂(A+|D|+R))` bits; hence `O(R³ log²(A+|D|))` bit-operations and no dependence on `Q` beyond `|D| ≤ Q`.
*Proof.* Operation counts are read off the algorithm. `|C(N,k)| ≤ (|N|+k)^k/k!` and `g_i ≤ (A+i)^i/i!` give the bit bound; the sum of `d+1` such products adds `log₂(d+1)` bits. ∎
Exactness: the closed route equals the frozen producer on all 163,912 calls of the box `Q ≤ 7, A ≤ 3, R ≤ 4` (same box as Theorem 2.1).

Measured worst case over all `(|D|, f)`, `|D| ≤ Q`:

| `(A,R,Q)` | mul / div / add | bit-ops (mul+div+add) | peak bits | `T_enum` indicator tests |
|---|---|---|---|---|
| (17,5,80) | 14 / 8 / 5 | 979 | 22 | 24,685,131 (×80 coordinate ops) |
| (15,8,80) | 23 / 14 / 8 | 2,914 | 34 | 389,575,972,971 |
| (7,4,40) | 11 / 6 / 4 | 356 | 15 | 76,155 |

## 4. Centered-line skip count (B5-K4)

At `|D| = 2A+R`, every orbit column with `R−|E|` odd carries the zero polynomial over ℤ (B5-M3), so a route that consults the parity before computing skips those amplitudes with no loss. The number of such columns among the `Σ_{1≤e≤R} C(|D|,e)` candidates is `Σ_{e≡R+1 (mod 2), 1≤e≤R} C(2A+R, e)`:

| `(A,R)` | `|D|` | candidates | identically zero | fraction | extra zero mod 3 (Kummer, B5-M8) |
|---|---|---|---|---|---|
| (17,5) | 39 | 667,927 | 82,992 | 12.4 % | +39 |
| (15,8) | 38 | 64,869,363 | 13,130,672 | 20.2 % | +2,834,496 |
| (7,4) | 18 | 4,047 | 834 | 20.6 % | 0 |

The fraction is of *columns*, weighted by `C(|D|,e)`, and is dominated by `e = R`; "half the classes vanish" is true of `|E|`-classes, not of columns. The residue-zero columns are a separate count: skipping them is valid only in the residue ring at that precision (B4-R2).

## 5. What is and is not claimed

- **Claimed (B5-K1, K2):** for the *reference producer*, the closed route is exponentially cheaper in `Q` than the enumeration route, by Theorems 2.1 and 3.1, with all BCM-1 charges stated; the two compute the same integer on the checked box and agree with the proved identity B5-M7 everywhere.
- **Claimed (B5-K3):** the measured BCM-1 counts in §3 are the actual counts of `evidence/pb/cost_theorem.py` on this host.
- **Claimed (B5-K4):** the exact skip counts of §4.
- **Not claimed:** anything about the native SAT execution. The native `entry` is `noncomputable` in the pinned Lean and its executable realisation, representation and ring arithmetic are unbound here. A speedup of a Python reference producer is not a native algorithmic improvement; the reference's enumeration is one way of evaluating the definition, not the native algorithm's cost. No asymptotic statement about the SAT algorithm follows.
- **Not charged:** the owner-sum lookups, index preparation and ring row assembly (B5's three routes); those costs are unchanged by this result and remain in `evidence/owner_results.json`.
