"""Search adverse boundaries of the ordered-unit-edge conjecture."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Iterable

try:
    from model.capacity_blocked import (
        Graph,
        System,
        capacity_vectors,
        directed_simple_graphs,
        ordered_multidags,
    )
except ModuleNotFoundError:  # Direct ``python model/...py`` execution.
    from capacity_blocked import (
        Graph,
        System,
        capacity_vectors,
        directed_simple_graphs,
        ordered_multidags,
    )


def transition_cycle(system: System, initial: tuple[int, ...]) -> bool:
    graph = system.reachable(initial)
    visiting: set[tuple[int, ...]] = set()
    visited: set[tuple[int, ...]] = set()

    def visit(state: tuple[int, ...]) -> bool:
        if state in visiting:
            return True
        if state in visited:
            return False
        visiting.add(state)
        if any(visit(nxt) for _, nxt in graph[state]):
            return True
        visiting.remove(state)
        visited.add(state)
        return False

    return visit(initial)


def record(system: System, initial: tuple[int, ...]) -> dict[str, object]:
    graph = system.reachable(initial)
    return {
        "arcs": system.graph.arcs,
        "sink": system.graph.sink,
        "capacity": system.capacity,
        "initial": initial,
        "legal": system.legal_firings(initial),
        "conflicts": system.capacity_conflicts(initial),
        "normal_forms": system.normal_forms(initial),
        "reachable_states": len(graph),
        "has_transition_cycle": transition_cycle(system, initial),
    }


def first_nonconfluent(
    graphs: Iterable[Graph], extra_capacity: int = 1
) -> dict[str, object] | None:
    candidates: list[dict[str, object]] = []
    for graph in graphs:
        for capacity in capacity_vectors(graph, extra_capacity):
            system = System(graph, tuple(capacity))
            for initial in system.states():
                if len(system.normal_forms(initial)) > 1:
                    candidates.append(record(system, tuple(initial)))
        if candidates:
            break
    if not candidates:
        return None
    return min(
        candidates,
        key=lambda item: (
            sum(sum(row) for row in item["arcs"]) + sum(item["sink"]),
            sum(item["capacity"]),
            sum(item["initial"]),
            item["arcs"],
            item["sink"],
            item["capacity"],
            item["initial"],
        ),
    )


def first_false_normal_form(graphs: Iterable[Graph], extra_capacity: int = 1) -> dict[str, object] | None:
    """Find a capacity normal form containing an ordinary unstable vertex."""

    candidates: list[dict[str, object]] = []
    for graph in graphs:
        for capacity in capacity_vectors(graph, extra_capacity):
            system = System(graph, tuple(capacity))
            for state in system.states():
                ordinary_unstable = tuple(
                    u for u in range(graph.n) if state[u] >= graph.outdegree(u)
                )
                if ordinary_unstable and not system.legal_firings(state):
                    item = record(system, tuple(state))
                    item["ordinary_unstable"] = ordinary_unstable
                    candidates.append(item)
        if candidates:
            break
    if not candidates:
        return None
    return min(
        candidates,
        key=lambda item: (
            sum(sum(row) for row in item["arcs"]) + sum(item["sink"]),
            sum(item["capacity"]),
            sum(item["initial"]),
            item["arcs"],
            item["sink"],
            item["capacity"],
            item["initial"],
        ),
    )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    payload = {
        "schema": "cbmd.capacity_blocked.boundaries.v1",
        "cyclic_simple_n2_false_normal_form": first_false_normal_form(
            directed_simple_graphs(2)
        ),
        "cyclic_simple_n2_nonconfluent": first_nonconfluent(directed_simple_graphs(2)),
        "cyclic_simple_n3_nonconfluent": first_nonconfluent(directed_simple_graphs(3)),
        "parallel_dag_n2_false_normal_form": first_false_normal_form(
            ordered_multidags(2, max_multiplicity=2)
        ),
        "parallel_dag_n2_nonconfluent": first_nonconfluent(
            ordered_multidags(2, max_multiplicity=2)
        ),
    }
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )


if __name__ == "__main__":
    main()

