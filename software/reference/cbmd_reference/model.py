"""Executable values and the explicitly limited BCM-1 arithmetic meter.

The recurrence and meter mirror MasterNumeratorBCM1.lean and
BCM1CostSemantics.lean.  In particular A=0 does not skip recurrence operations.
BCM-1 charges the two coefficient recurrences, convolution, and final scale.
It does not charge integer bit complexity, control flow, parameter arithmetic,
unary signs, powers, comparisons, construction, indexing, or memory.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable


def natural(name: str, value: int) -> None:
    if type(value) is not int or value < 0:
        raise ValueError(f"{name} must be a nonnegative integer (booleans refused)")


def scalar_parameters(a: int, r: int, delta: int, f: int) -> None:
    for name, value in (("A", a), ("R", r), ("delta", delta), ("f", f)):
        natural(name, value)
    if r == 0 or f >= r:
        raise ValueError("this public scalar API supports R >= 1 and 0 <= f < R")


@dataclass(frozen=True)
class BCM1Counts:
    mul: int = 0
    div: int = 0
    add: int = 0


@dataclass(frozen=True)
class BCM1Result:
    value: int
    counts: BCM1Counts
    choose_table: tuple[int, ...] = ()
    negative_table: tuple[int, ...] = ()
    branch: str = "SCALAR"


class _Meter:
    def __init__(self) -> None:
        self.mul = self.div = self.add = 0

    def multiply(self, left: int, right: int) -> int:
        self.mul += 1
        return left * right

    def divide(self, numerator: int, denominator: int) -> int:
        self.div += 1
        quotient, remainder = divmod(numerator, denominator)
        if remainder:
            raise ArithmeticError("BCM-1 recurrence division was not exact")
        return quotient

    def plus(self, left: int, right: int) -> int:
        self.add += 1
        return left + right

    def counts(self) -> BCM1Counts:
        return BCM1Counts(self.mul, self.div, self.add)


def master_numerator(a: int, r: int, delta: int, f: int) -> BCM1Result:
    """Evaluate the master numerator and report the actual declared charges.

    Here delta is active-set cardinality; f is mismatch cardinality minus one
    when transported to an eligible native entry.  The scalar formula itself
    also supports nonnegative delta values outside that native interpretation.
    """
    scalar_parameters(a, r, delta, f)
    degree = r - 1 - f
    upper = a + r - delta
    meter = _Meter()
    choose = [1]
    negative = [1]
    for k in range(degree):
        choose.append(meter.divide(meter.multiply(choose[-1], upper - k), k + 1))
        negative.append(meter.divide(meter.multiply(negative[-1], a + k), k + 1))
    total = 0
    for k in range(degree + 1):
        total = meter.plus(total, meter.multiply(choose[k], negative[degree - k]))
    if a % 2:
        total = -total
    value = meter.multiply(2 ** (r - 1), total)
    return BCM1Result(value, meter.counts(), tuple(choose), tuple(negative))


@dataclass(frozen=True)
class UniversalState:
    """Finite-color native state: one head word and a tuple of slot words."""

    head: tuple[int, ...]
    slots: tuple[tuple[int, ...], ...]
    colors: int = 2

    def __post_init__(self) -> None:
        natural("colors", self.colors)
        if self.colors == 0:
            raise ValueError("colors must be positive")
        if not isinstance(self.head, tuple) or not self.head:
            raise ValueError("head must be a nonempty tuple")
        if not isinstance(self.slots, tuple) or not self.slots:
            raise ValueError("slots must be a nonempty tuple of words")
        for word in (self.head,) + self.slots:
            if not isinstance(word, tuple) or len(word) != len(self.head):
                raise ValueError("every slot must be a tuple with the head's length")
            for color in word:
                natural("color", color)
                if color >= self.colors:
                    raise ValueError("color outside the declared finite alphabet")


def _pair(i: int, u: UniversalState, y: UniversalState | None = None) -> None:
    natural("slot index", i)
    if not isinstance(u, UniversalState) or i >= len(u.slots):
        raise ValueError("invalid state or selected slot index")
    if y is not None and (
        not isinstance(y, UniversalState)
        or len(y.head) != len(u.head)
        or len(y.slots) != len(u.slots)
        or y.colors != u.colors
    ):
        raise ValueError("states must have identical dimensions and color alphabet")


def swap_positions(i: int, positions: Iterable[int], u: UniversalState) -> UniversalState:
    _pair(i, u)
    coordinates = tuple(positions)
    for coordinate in coordinates:
        natural("coordinate", coordinate)
        if coordinate >= len(u.head):
            raise ValueError("coordinate outside the word")
    selected = frozenset(coordinates)
    head = tuple(u.slots[i][l] if l in selected else x for l, x in enumerate(u.head))
    slots = tuple(
        tuple(u.head[l] if j == i and l in selected else x for l, x in enumerate(word))
        for j, word in enumerate(u.slots)
    )
    return UniversalState(head, slots, u.colors)


def active_set(i: int, u: UniversalState) -> frozenset[int]:
    _pair(i, u)
    return frozenset(l for l, x in enumerate(u.head) if x != u.slots[i][l])


def mismatches(i: int, u: UniversalState, y: UniversalState) -> frozenset[int]:
    _pair(i, u, y)
    # Native mismatches compare COLUMN HEAD to ROW SELECTED SLOT.
    return frozenset(l for l, x in enumerate(y.head) if x != u.slots[i][l])


def orbit_compatible(i: int, u: UniversalState, y: UniversalState) -> bool:
    """CoordinateOrbitBCM1.OrbitCompatible, including all unselected slots."""
    _pair(i, u, y)
    if any(u.slots[j] != y.slots[j] for j in range(len(u.slots)) if j != i):
        return False
    return all(
        (y.head[l], y.slots[i][l]) in
        ((u.head[l], u.slots[i][l]), (u.slots[i][l], u.head[l]))
        for l in range(len(u.head))
    )


def joint_entry(i: int, t: int, a: int, r: int,
                u: UniversalState, y: UniversalState) -> BCM1Result:
    """Coordinate joint candidate, refusing values outside a common Joint fiber.

    Both states must have the same head color at t, different from their own
    selected-slot color.  Returned counts cover only the scalar kernel; a zero
    branch reports zero *scalar* arithmetic, not a free orbit/support test.
    """
    _pair(i, u, y)
    natural("pivot", t)
    natural("A", a)
    natural("R", r)
    if r == 0 or t >= len(u.head):
        raise ValueError("joint API requires R >= 1 and an in-range pivot")
    if (u.head[t] != y.head[t] or u.slots[i][t] == u.head[t]
            or y.slots[i][t] == y.head[t]):
        raise ValueError("both states must belong to the same native Joint fiber")
    if not orbit_compatible(i, u, y):
        return BCM1Result(0, BCM1Counts(), branch="OUTSIDE_ORBIT")
    mismatch_count = len(mismatches(i, u, y))
    if mismatch_count > r:
        return BCM1Result(0, BCM1Counts(), branch="ABOVE_MISMATCH_SUPPORT")
    return master_numerator(a, r, len(active_set(i, u)), mismatch_count - 1)
