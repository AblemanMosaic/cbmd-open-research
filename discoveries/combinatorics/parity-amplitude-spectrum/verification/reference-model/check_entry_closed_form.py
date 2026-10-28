"""Exact finite audit of LayoutNumerator.entry and the proposed closed form.

This mirrors only the head/selected-slot coordinates used by the pinned Lean
definitions.  It uses Fraction arithmetic to construct the same integer parity
coefficients and enumerates the literal difference expansion.
"""
from __future__ import annotations

from fractions import Fraction
from itertools import combinations, product
import hashlib
import json
from pathlib import Path


def choose(n: int, k: int) -> int:
    if k < 0 or k > n:
        return 0
    result = 1
    for i in range(1, k + 1):
        result = result * (n - i + 1) // i
    return result


def nat_sub(a: int, b: int) -> int:
    return max(a - b, 0)


def parity_coefficients(A: int, R: int) -> list[int]:
    matrix = [[Fraction(choose(A + d, j)) for j in range(R)] for d in range(R)]
    target = [Fraction((-1) ** (A + d)) for d in range(R)]
    for col in range(R):
        pivot = next(row for row in range(col, R) if matrix[row][col])
        matrix[col], matrix[pivot] = matrix[pivot], matrix[col]
        target[col], target[pivot] = target[pivot], target[col]
        scale = matrix[col][col]
        matrix[col] = [value / scale for value in matrix[col]]
        target[col] /= scale
        for row in range(R):
            if row == col:
                continue
            scale = matrix[row][col]
            if scale:
                matrix[row] = [x - scale * y for x, y in zip(matrix[row], matrix[col])]
                target[row] -= scale * target[col]
    assert all(value.denominator == 1 for value in target)
    return [int(value) for value in target]


State = tuple[tuple[int, int], ...]


def swap(state: State, positions: tuple[int, ...] | set[int]) -> State:
    selected = set(positions)
    return tuple((slot, head) if i in selected else (head, slot)
                 for i, (head, slot) in enumerate(state))


def subsets(values: tuple[int, ...], size: int | None = None):
    sizes = range(len(values) + 1) if size is None else (size,)
    for length in sizes:
        yield from combinations(values, length)


def active_set(u: State) -> set[int]:
    return {i for i, (head, slot) in enumerate(u) if head != slot}


def mismatches(u: State, y: State) -> set[int]:
    return {i for i, ((_, slot), (head_y, _)) in enumerate(zip(u, y)) if head_y != slot}


def integer_difference_expansion(S: tuple[int, ...], y: State, x: State) -> int:
    return sum(((-1) ** len(B)) * int(swap(x, B) == y) for B in subsets(S))


def entry(t: int, A: int, R: int, u: State, y: State) -> int:
    coefficients = parity_coefficients(A, R)
    L = tuple(i for i in range(len(u)) if i != t)
    base = swap(u, L)
    return sum(
        coefficients[j] * (2 ** (R - 1 - j)) *
        sum(integer_difference_expansion(S, y, base) for S in subsets(L, j))
        for j in range(R)
    )


def lean_statement_form(t: int, A: int, R: int, u: State, y: State) -> int:
    del t
    coefficients = parity_coefficients(A, R)
    n = len(active_set(u))
    m = len(mismatches(u, y))
    required = nat_sub(m, 1)
    return ((-1) ** required) * sum(
        coefficients[j] * (2 ** (R - 1 - j)) *
        choose(nat_sub(n, m), nat_sub(j, required))
        for j in range(R)
    )


def corrected_form(t: int, A: int, R: int, u: State, y: State) -> int:
    del t
    coefficients = parity_coefficients(A, R)
    n = len(active_set(u))
    m = len(mismatches(u, y))
    required = nat_sub(m, 1)
    return ((-1) ** required) * sum(
        coefficients[j] * (2 ** (R - 1 - j)) *
        (choose(nat_sub(n, m), j - required) if required <= j else 0)
        for j in range(R)
    )


def encoded(state: State) -> list[list[int]]:
    return [list(pair) for pair in state]


comparisons = 0
states = 0
first_without_ht = None
first_literal_statement_counterexample = None
mutant_active_detected = 0
mutant_sign_detected = 0

for Q in range(1, 6):
    for flat in product((0, 1), repeat=2 * Q):
        u = tuple((flat[2 * i], flat[2 * i + 1]) for i in range(Q))
        states += 1
        D = tuple(sorted(active_set(u)))
        orbit = {swap(u, T) for T in subsets(D)}
        for y in orbit:
            M = mismatches(u, y)
            for t in range(Q):
                for A in range(3):
                    for R in range(1, 4):
                        lhs = entry(t, A, R, u, y)
                        literal_rhs = lean_statement_form(t, A, R, u, y)
                        corrected_rhs = corrected_form(t, A, R, u, y)
                        if t in M:
                            comparisons += 1
                            assert lhs == corrected_rhs, (Q, t, A, R, u, y, lhs, corrected_rhs)
                            if lhs != literal_rhs and first_literal_statement_counterexample is None:
                                first_literal_statement_counterexample = {
                                    "Q": Q, "t": t, "A": A, "R": R,
                                    "u": encoded(u), "y": encoded(y),
                                    "entry": lhs, "literal_statement_rhs": literal_rhs,
                                    "corrected_rhs": corrected_rhs,
                                    "mismatches": sorted(M), "active_set": sorted(D),
                                    "cause": "Nat subtraction truncates j-(m-1) to zero when j<m-1",
                                }
                            wrong_n = Q
                            required = nat_sub(len(M), 1)
                            mutant_active = ((-1) ** required) * sum(
                                parity_coefficients(A, R)[j] * 2 ** (R - 1 - j) *
                                (choose(nat_sub(wrong_n, len(M)), j - required)
                                 if required <= j else 0)
                                for j in range(R)
                            )
                            mutant_active_detected += int(mutant_active != lhs)
                            mutant_sign_detected += int(-corrected_rhs != lhs and corrected_rhs != 0)
                        elif first_without_ht is None and lhs != literal_rhs:
                            first_without_ht = {
                                "Q": Q, "t": t, "A": A, "R": R,
                                "u": encoded(u), "y": encoded(y),
                                "entry": lhs, "unlicensed_formula": literal_rhs,
                                "mismatches": sorted(M), "active_set": sorted(D),
                            }

assert first_without_ht is not None
assert first_literal_statement_counterexample is not None
assert mutant_active_detected > 0
assert mutant_sign_detected > 0

source_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
print(json.dumps({
    "schema": "cbmd.entry-closed-form-audit.v1",
    "status": "PASS",
    "statement_status": "REFUTED_AS_STATED",
    "source_sha256": source_sha256,
    "state_fixtures": states,
    "licensed_comparisons": comparisons,
    "active_cardinality_mutant_detections": mutant_active_detected,
    "sign_mutant_detections": mutant_sign_detected,
    "first_counterexample_without_ht": first_without_ht,
    "first_literal_statement_counterexample": first_literal_statement_counterexample,
    "corrected_statement": "replace choose(n-m, j-(m-1)) by 0 when j<m-1",
    "claim_boundary": "FINITE_BINARY_REFERENCE_AUDIT_OF_PINNED_DEFINITIONS",
    "authority_effect": "NONE",
}, sort_keys=True))
