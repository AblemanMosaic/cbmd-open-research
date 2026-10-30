# Jacobians of abelian Cayley digraphs: an answer to Reiner's question

> **Standing:** `PROVISIONAL_WRITTEN_ARGUMENT`, `EXACT_MODEL_VERIFIED`

Permanent claim ID: `CBMD-COMB-CAYLEY-JAC-001`

## The question

Let `A` be a finite abelian group, and `S` a multiset of nonzero elements
that sums to 0 and generates `A`. The Cayley digraph `Cay(A, S)` is the
McKay quiver of the corresponding representation. Benkart, Klivans and
Reiner showed that its Jacobian (sandpile group) always surjects onto `A`.
V. Reiner asked (BIRS sandpile-group workshop, open problem 1.9) whether
`Jac ≅ A` happens only in the obvious case: `A` cyclic and `S = {a, −a}`,
where the digraph is just a cycle.

## What this dossier records

**Answer: yes.** `argument/WRITTEN_ARGUMENT.md` gives a written proof that
`|Jac(Cay(A, S))| > |A|` whenever `A` is not cyclic or `|S| ≥ 3`. Moreover:

- if `A` is cyclic of order `n` and `|S| ≥ 3`, then
  `|Jac| ≥ (3/2)^{φ(n)} · n`;
- if the `p`-part of `A` is not cyclic, then `p^{2 + v_p(n)}` divides `|Jac|`.

The proof uses only the order of the Jacobian:

1. **Product formula.** By the matrix-tree theorem,
   `n·|Jac| = Π_{χ≠1} (|S| − Σ_{x∈S} χ(x))`.
2. **Grouping into norms.** Grouping the characters into Galois orbits turns
   this into a product of cyclotomic norms, one for each cyclic quotient of
   `A`.
3. **Prime-power quotients.** By the sum-zero condition, each norm for a
   cyclic quotient of order `p^k` is divisible by `p²`.
4. **Non-cyclic `A`.** Counting cyclic quotients rules out non-cyclic `A`.
5. **Three or more elements.** An AM–GM bound on the norm of a sum of terms
   `1 − ζ` rules out `|S| ≥ 3`.

**Checks.**

- An exact Smith-normal-form scan over all abelian groups of order at most 24
  and all multisets with `|S| ≤ 5` (32,551 cases), and over order at most 14
  with `|S| ≤ 7` (19,633 cases). It finds `Jac ≅ A` only in the cyclic
  `{a, −a}` cases.
- Separate checks of every proof ingredient: the product formula, the
  orbit-norm factorisation with exact resultants, the `p²`-divisibility, the
  AM–GM bound, and the subgroup count for non-cyclic `p`-groups.

## What is not established

- An independent specialist review of the proof.
- The non-abelian version of the question, for McKay quivers of
  non-abelian groups and `G^{ab}`.
- The full structure of `Jac` beyond its order.

## Reproduction

```text
python -B discoveries/combinatorics/cayley-digraph-jacobian/verification/reference/check_cayley_jacobian.py
cd discoveries/combinatorics/cayley-digraph-jacobian/verification/reference
python3 cayley_jac.py 24 5      # exhaustive scan, about 40 s
python3 check_bound.py 16 5     # product formula and bounds
python3 check_norms.py 18 4     # exact orbit norms (cyclic groups)
```
