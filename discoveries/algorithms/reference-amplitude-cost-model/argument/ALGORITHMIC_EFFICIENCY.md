# Algorithmic efficiency in the reference model: three provable results (r6)

Scope: reference model (`src/owner_sum.py` producer), cost model BCM-1 for big integers, ring-operation counts for polynomial arithmetic. Evidence `evidence/pb/efficiency.py`, `evidence/pb/efficiency.json`. **No native claim** (see §4).

## T1 — Spectrum table theorem (B5-K5)

**Theorem.** Fix `(A, R, Q)`. The integer amplitude of every source row for every target `u` with `|D(u)| ≤ Q` and every orbit column `y` with `1 ≤ |E(y)| ≤ R` is an entry of the table `T[δ][f] = n(A,R,δ,f)`, `1 ≤ δ ≤ Q`, `0 ≤ f < min(R,δ)`, which has at most `Q·R` entries and is computable by the master formula (B5-M7) in `O(Q·R²)` BCM-1 big-integer operations on `O(R log(A+Q))`-bit integers.
*Proof.* Pivot independence and dependence on `(δ, f)` only is Lemma 2.2 (r2); each entry costs `O(R)` by B5-K1. ∎

Measured: `(17,5,80)` → 390 entries, 3,150 mul / 1,580 div / 1,180 add, peak 22 bits. The frozen producer spends `24,685,131` indicator tests **per amplitude call** (B5-K2). A qualifying off-diagonal row invokes that producer once for each pivot in `E`; the table replaces those repeated amplitude calls and is shared by all `2^160` targets and all their columns.

## T2 — Row assembly identity (B5-K6)

**Theorem.** For `y` in the orbit with `1 ≤ |E| ≤ R`,
`source_row(u,y) = [y=u] − (n/2^{R−1}) · (1 − Π_{s∈E} (1 − x/(s+1)))`,
and the right-hand side is computable from `T` in `O(|E|²)` ring operations (one product of `|E|` linear factors), using one inverse of `2^{R−1}` and one inverse of each node factor `s+1` for `s∈E`. The identity is an executable ring formula only when all of those elements are units, or when their inverses are supplied as separately checked input.
*Proof.* `Σ_{t∈E} L_t(x)`, with `L_t` the Lagrange factor vanishing at 0 and at nodes `s+1 ≠ t+1`, is the unique polynomial of degree ≤ `|E|` equal to 1 at every node `s+1` and 0 at 0, i.e. `1 − Π(1 − x/(s+1))` (B4-F1's `φ_E − 1`). Pivot independence of `n` lets the sum factor. ∎

Exactness: equals the frozen `source_row` on 10,476 orbit rows over `Q ≤ 4, A ≤ 2, R ≤ 3`, rationals and `Z/25`, 0 mismatches. This modular box has only node factors `1,2,3,4`, all units modulo 25. New adverse controls refuse node 5 modulo 25 and the denominator 2 modulo 8; they test the unit boundary rather than extending the equality box.
Honest accounting: the ring-operation counts are **comparable** (closed 120,876 vs reference 123,588 on that box); the reference's Lagrange route is already `O(|E|²)` per pivot. The saving of T2 is the removal of up to `|E|` numerator enumerations per qualifying off-diagonal row (80,628 indicator tests on the checked box; `|E|·24.7M` when all `|E|` amplitude calls are active at `Q=80,R=5`), not the polynomial arithmetic.

## T3 — Row-centric versus owner-centric owner sums (B5-K7, mostly negative)

For a fixed covered target, the nonzero owner sums are exactly the rows at the live columns: `1 + Σ_{1≤e≤R} C(|D|,e)`, minus the centered-line parity class when `|D| = 2A+R`. A row-centric pass computes all of them in that many row assemblies plus owner lookups; the owner-centric candidate route (B5) costs one candidate construction (`Q` coordinate tests), one vertex lookup and at most one row assembly **per requested owner**.

| `(A,R,Q)` | `|D|` | live columns | row-centric wins only if |
|---|---|---|---|
| (17,5,80) | 6 | 63 | `|V| > 63` |
| (17,5,80) | 39 (centered) | 584,936 | `|V| > 584,936` |
| (17,5,80) | 40 | 760,099 | `|V| > 760,099` |
| (15,8,80) | 38 (centered) | 51,738,692 | `|V| > 5.2×10⁷` |
| (7,4,40) | 18 (centered) | 3,214 | `|V| > 3,214` |

Conclusion: at the typical mismatch count `|D| ≈ Q/2` the owner-centric route of B5-M1 is the right design unless the number of owners is enormous; row-centric wins only for small `|D|`. This is recorded as a result, not hidden.

## 4. Nonclaims

- Nothing about the native SAT execution: `entry` is `noncomputable` in the pinned source; representation, memory and ring arithmetic are unbound. T1–T3 bound and compare evaluation strategies of the *reference definition*.
- Ring-operation counts are polynomial-arithmetic counts in the package's `Ring` class, not bit costs; BCM-1 applies to the big-integer table only.
- T2 requires `2^{R−1}` and every node factor `s+1` used in the product to be units in the execution ring; exact integer amplitudes alone do not supply those inverses.
- No wall-clock claim.
