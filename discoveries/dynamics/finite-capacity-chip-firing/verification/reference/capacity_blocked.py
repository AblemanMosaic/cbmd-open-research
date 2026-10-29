"""Exact reference model for capacity-blocked chip-firing.

The code intentionally uses only Python's standard library.  It is a finite
model and does not prove any unbounded mathematical statement.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import Iterable, Iterator

State = tuple[int, ...]


@dataclass(frozen=True)
class Graph:
    """Loopless directed multigraph with an implicit absorbing sink."""

    arcs: tuple[tuple[int, ...], ...]
    sink: tuple[int, ...]

    def __post_init__(self) -> None:
        n = len(self.arcs)
        if len(self.sink) != n or any(len(row) != n for row in self.arcs):
            raise ValueError("arcs must be square and sink must have length n")
        if any(x < 0 for row in self.arcs for x in row) or any(x < 0 for x in self.sink):
            raise ValueError("edge multiplicities must be nonnegative")
        if any(self.arcs[u][u] for u in range(n)):
            raise ValueError("self-loops are excluded from this cycle")
        if any(self.outdegree(u) == 0 for u in range(n)):
            raise ValueError("every nonsink vertex must have positive outdegree")

    @property
    def n(self) -> int:
        return len(self.arcs)

    def outdegree(self, u: int) -> int:
        return self.sink[u] + sum(self.arcs[u])

    def edge_count(self) -> int:
        return sum(sum(row) for row in self.arcs) + sum(self.sink)

    def is_ordered_dag(self) -> bool:
        return all(self.arcs[u][v] == 0 for u in range(self.n) for v in range(u + 1))

    def all_reach_sink(self) -> bool:
        reaches = [False] * self.n
        for u in range(self.n - 1, -1, -1):
            reaches[u] = self.sink[u] > 0 or any(
                self.arcs[u][v] > 0 and reaches[v] for v in range(u + 1, self.n)
            )
        return all(reaches)

    def all_reach_sink_general(self) -> bool:
        """Return whether every vertex has a directed path to the sink."""

        reaches = [edge_count > 0 for edge_count in self.sink]
        changed = True
        while changed:
            changed = False
            for u in range(self.n):
                if reaches[u]:
                    continue
                if any(self.arcs[u][v] > 0 and reaches[v] for v in range(self.n)):
                    reaches[u] = True
                    changed = True
        return all(reaches)

    def decreasing_weights(self) -> tuple[int, ...]:
        """Return weights making every firing strictly decrease weighted mass.

        This construction is valid for ordered DAGs.  Sink chips have weight 0.
        """

        if not self.is_ordered_dag():
            raise ValueError("weight construction requires an ordered DAG")
        weights = [0] * self.n
        for u in range(self.n - 1, -1, -1):
            downstream = sum(self.arcs[u][v] * weights[v] for v in range(u + 1, self.n))
            weights[u] = downstream + 1
        return tuple(weights)


@dataclass(frozen=True)
class System:
    graph: Graph
    capacity: tuple[int, ...]

    def __post_init__(self) -> None:
        if len(self.capacity) != self.graph.n or any(c < 0 for c in self.capacity):
            raise ValueError("capacity must be a nonnegative n-tuple")

    def states(self) -> Iterator[State]:
        return product(*(range(c + 1) for c in self.capacity))

    def validate_state(self, state: State) -> None:
        if len(state) != self.graph.n:
            raise ValueError("state length mismatch")
        if any(x < 0 or x > c for x, c in zip(state, self.capacity)):
            raise ValueError("state outside capacity box")

    def legal(self, state: State, u: int) -> bool:
        self.validate_state(state)
        if state[u] < self.graph.outdegree(u):
            return False
        return all(
            state[v] + self.graph.arcs[u][v] <= self.capacity[v]
            for v in range(self.graph.n)
        )

    def legal_firings(self, state: State) -> tuple[int, ...]:
        return tuple(u for u in range(self.graph.n) if self.legal(state, u))

    def fire(self, state: State, u: int) -> State:
        if not self.legal(state, u):
            raise ValueError(f"illegal firing {u} from {state}")
        result = list(state)
        result[u] -= self.graph.outdegree(u)
        for v in range(self.graph.n):
            result[v] += self.graph.arcs[u][v]
        fired = tuple(result)
        self.validate_state(fired)
        return fired

    def successors(self, state: State) -> tuple[tuple[int, State], ...]:
        return tuple((u, self.fire(state, u)) for u in self.legal_firings(state))

    def reachable(self, initial: State) -> dict[State, tuple[tuple[int, State], ...]]:
        self.validate_state(initial)
        todo = deque([initial])
        seen: dict[State, tuple[tuple[int, State], ...]] = {}
        while todo:
            state = todo.popleft()
            if state in seen:
                continue
            next_states = self.successors(state)
            seen[state] = next_states
            for _, nxt in next_states:
                if nxt not in seen:
                    todo.append(nxt)
        return seen

    def normal_forms(self, initial: State) -> tuple[State, ...]:
        graph = self.reachable(initial)
        return tuple(sorted(state for state, succ in graph.items() if not succ))

    def is_confluent_from(self, initial: State) -> bool:
        return len(self.normal_forms(initial)) == 1

    def capacity_conflicts(self, state: State) -> tuple[tuple[int, int, int], ...]:
        """Return legal firing pairs whose combined demand overflows receiver v."""

        legal = self.legal_firings(state)
        conflicts: list[tuple[int, int, int]] = []
        for i, u in enumerate(legal):
            for w in legal[i + 1 :]:
                for v in range(self.graph.n):
                    demand = self.graph.arcs[u][v] + self.graph.arcs[w][v]
                    if state[v] + demand > self.capacity[v]:
                        conflicts.append((u, w, v))
        return tuple(conflicts)

    def has_reachable_capacity_conflict(self, initial: State) -> bool:
        return any(self.capacity_conflicts(state) for state in self.reachable(initial))


def ordered_simple_dags(n: int) -> Iterable[Graph]:
    """Enumerate unit-edge ordered DAGs whose every vertex reaches the sink."""

    nonsink_slots = [(u, v) for u in range(n) for v in range(u + 1, n)]
    slots = [("edge", u, v) for u, v in nonsink_slots] + [("sink", u, n) for u in range(n)]
    for bits in product((0, 1), repeat=len(slots)):
        arcs = [[0] * n for _ in range(n)]
        sink = [0] * n
        for bit, (kind, u, v) in zip(bits, slots):
            if not bit:
                continue
            if kind == "edge":
                arcs[u][v] = 1
            else:
                sink[u] = 1
        try:
            graph = Graph(tuple(tuple(row) for row in arcs), tuple(sink))
        except ValueError:
            continue
        if graph.all_reach_sink():
            yield graph


def capacity_vectors(graph: Graph, extra: int = 1) -> Iterable[tuple[int, ...]]:
    """Enumerate capacities d(u)..d(u)+extra in lexicographic order."""

    return product(*(range(graph.outdegree(u), graph.outdegree(u) + extra + 1) for u in range(graph.n)))


def directed_simple_graphs(n: int) -> Iterable[Graph]:
    """Enumerate loopless unit-edge digraphs with sink reachability."""

    slots = [("edge", u, v) for u in range(n) for v in range(n) if u != v]
    slots += [("sink", u, n) for u in range(n)]
    for bits in product((0, 1), repeat=len(slots)):
        arcs = [[0] * n for _ in range(n)]
        sink = [0] * n
        for bit, (kind, u, v) in zip(bits, slots):
            if not bit:
                continue
            if kind == "edge":
                arcs[u][v] = 1
            else:
                sink[u] = 1
        try:
            graph = Graph(tuple(tuple(row) for row in arcs), tuple(sink))
        except ValueError:
            continue
        if graph.all_reach_sink_general():
            yield graph


def ordered_multidags(n: int, max_multiplicity: int = 2) -> Iterable[Graph]:
    """Enumerate ordered DAGs with bounded nonsink multiplicity and unit sink edges."""

    nonsink_slots = [(u, v) for u in range(n) for v in range(u + 1, n)]
    for edge_values in product(range(max_multiplicity + 1), repeat=len(nonsink_slots)):
        for sink_values in product((0, 1), repeat=n):
            arcs = [[0] * n for _ in range(n)]
            for value, (u, v) in zip(edge_values, nonsink_slots):
                arcs[u][v] = value
            try:
                graph = Graph(tuple(tuple(row) for row in arcs), tuple(sink_values))
            except ValueError:
                continue
            if graph.all_reach_sink():
                yield graph

