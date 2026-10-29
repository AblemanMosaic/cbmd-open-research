"""Separately coded finite oracles; no frozen producer or recurrence imports.

Scalar values use falling factorials. Native entries reconstruct the defining
parity interpolation system over Fraction and expand literal differences.
This is implementation diversity inside the project, not external review.
"""

from __future__ import annotations

from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import comb, factorial, prod

from .model import UniversalState, scalar_parameters


def integer_choose(upper: int, lower: int) -> int:
    if type(upper) is not int or type(lower) is not int or lower < 0:
        raise ValueError("integer binomial requires integer upper and natural lower")
    numerator = prod(upper - j for j in range(lower))
    quotient, remainder = divmod(numerator, factorial(lower))
    if remainder:
        raise ArithmeticError("falling factorial quotient was not integral")
    return quotient


def formula_oracle(a: int, r: int, delta: int, f: int) -> int:
    scalar_parameters(a, r, delta, f)
    degree = r - 1 - f
    # The natural subtraction here is significant at A=k=0.
    total = sum(
        integer_choose(a + r - delta, k)
        * comb(max(a + degree - k - 1, 0), degree - k)
        for k in range(degree + 1)
    )
    return (-1) ** a * 2 ** (r - 1) * total


@lru_cache(maxsize=None)
def parity_coefficients(a: int, r: int) -> tuple[int, ...]:
    scalar_parameters(a, r, 0, 0)
    rows = [
        [Fraction(comb(a + row, j)) for j in range(r)]
        + [Fraction((-1) ** (a + row))]
        for row in range(r)
    ]
    for column in range(r):
        pivot = next(row for row in range(column, r) if rows[row][column])
        rows[column], rows[pivot] = rows[pivot], rows[column]
        divisor = rows[column][column]
        rows[column] = [x / divisor for x in rows[column]]
        for row in range(r):
            if row != column:
                factor = rows[row][column]
                rows[row] = [x - factor * y for x, y in zip(rows[row], rows[column])]
    answer = tuple(row[-1] for row in rows)
    if any(value.denominator != 1 for value in answer):
        raise ArithmeticError("parity interpolation did not return integers")
    return tuple(int(value) for value in answer)


def interpolation_oracle(a: int, r: int, f: int, m: int) -> int:
    """Signed centered amplitude for delta=f+m+1; includes m=0."""
    scalar_parameters(a, r, f + m + 1, f)
    if type(m) is not int or m < 0:
        raise ValueError("m must be a nonnegative integer")
    return (-1) ** f * sum(
        coefficient * 2 ** (r - 1 - j) * comb(m, j - f)
        for j, coefficient in enumerate(parity_coefficients(a, r))
        if f <= j and j - f <= m
    )


def _mask_swap(i: int, mask: int, u: UniversalState) -> UniversalState:
    # Deliberately separate from model.swap_positions.
    head = list(u.head)
    slots = [list(word) for word in u.slots]
    for coordinate in range(len(head)):
        if mask & (1 << coordinate):
            head[coordinate], slots[i][coordinate] = slots[i][coordinate], head[coordinate]
    return UniversalState(tuple(head), tuple(tuple(word) for word in slots), u.colors)


def orbit_oracle(i: int, u: UniversalState, y: UniversalState) -> bool:
    return any(_mask_swap(i, mask, u) == y for mask in range(1 << len(u.head)))


def native_entry_oracle(i: int, t: int, a: int, r: int,
                        u: UniversalState, y: UniversalState) -> int:
    """Literal source expansion; deliberately exponential and for small audits."""
    scalar_parameters(a, r, 0, 0)
    coordinates = tuple(l for l in range(len(u.head)) if l != t)
    base_mask = sum(1 << l for l in coordinates)
    base = _mask_swap(i, base_mask, u)
    value = 0
    for j, coefficient in enumerate(parity_coefficients(a, r)):
        differences = 0
        for selected in combinations(coordinates, j):
            # Expand product of (1 - swap_l) against the exact state delta.
            for submask in range(1 << len(selected)):
                mask = sum(1 << l for k, l in enumerate(selected) if submask & (1 << k))
                differences += (-1) ** submask.bit_count() * int(_mask_swap(i, mask, base) == y)
        value += coefficient * 2 ** (r - 1 - j) * differences
    return value
