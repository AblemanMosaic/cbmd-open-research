"""Deterministic search for minimal nonconfluent capacity-blocked systems."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path

try:
    from model.capacity_blocked import System, capacity_vectors, ordered_simple_dags
except ModuleNotFoundError:  # Direct ``python model/...py`` execution.
    from capacity_blocked import System, capacity_vectors, ordered_simple_dags


@dataclass(frozen=True)
class Witness:
    n: int
    arcs: tuple[tuple[int, ...], ...]
    sink: tuple[int, ...]
    capacity: tuple[int, ...]
    initial: tuple[int, ...]
    normal_forms: tuple[tuple[int, ...], ...]
    reachable_states: int
    initial_legal: tuple[int, ...]
    initial_conflicts: tuple[tuple[int, int, int], ...]
    has_reachable_capacity_conflict: bool


def witness_key(w: Witness) -> tuple[object, ...]:
    edge_count = sum(sum(row) for row in w.arcs) + sum(w.sink)
    return (
        w.n,
        edge_count,
        sum(w.capacity),
        w.arcs,
        w.sink,
        w.capacity,
        sum(w.initial),
        w.initial,
    )


def find_witnesses(max_n: int, extra_capacity: int) -> tuple[list[Witness], dict[str, int]]:
    witnesses: list[Witness] = []
    stats = {"graphs": 0, "systems": 0, "initial_states": 0}
    for n in range(1, max_n + 1):
        for graph in ordered_simple_dags(n):
            stats["graphs"] += 1
            for capacity in capacity_vectors(graph, extra_capacity):
                stats["systems"] += 1
                system = System(graph, tuple(capacity))
                for initial in system.states():
                    stats["initial_states"] += 1
                    normal_forms = system.normal_forms(initial)
                    if len(normal_forms) <= 1:
                        continue
                    reachable = system.reachable(initial)
                    witnesses.append(
                        Witness(
                            n=n,
                            arcs=graph.arcs,
                            sink=graph.sink,
                            capacity=tuple(capacity),
                            initial=tuple(initial),
                            normal_forms=normal_forms,
                            reachable_states=len(reachable),
                            initial_legal=system.legal_firings(initial),
                            initial_conflicts=system.capacity_conflicts(initial),
                            has_reachable_capacity_conflict=system.has_reachable_capacity_conflict(initial),
                        )
                    )
        if witnesses:
            break
    return sorted(witnesses, key=witness_key), stats


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=4)
    parser.add_argument("--extra-capacity", type=int, default=1)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--limit", type=int, default=20)
    args = parser.parse_args()

    witnesses, stats = find_witnesses(args.max_n, args.extra_capacity)
    payload = {
        "schema": "cbmd.capacity_blocked.search.v1",
        "box": {
            "max_n": args.max_n,
            "extra_capacity": args.extra_capacity,
            "simple_ordered_dags": True,
            "unit_edges": True,
            "all_states": True,
        },
        "enumerated": stats,
        "witness_count": len(witnesses),
        "witnesses": [asdict(w) for w in witnesses[: args.limit]],
    }
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8", newline="\n")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()

