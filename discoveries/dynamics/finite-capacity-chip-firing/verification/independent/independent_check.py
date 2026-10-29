"""Independent finite verifier for Cycle 1.

This file intentionally does not import the producer in ``model/``.  It uses a
different graph encoding and a recursive terminal-set evaluator.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from functools import lru_cache
from pathlib import Path


def ordered_graphs(n: int):
    edges = [(u, v) for u in range(n) for v in range(u + 1, n)]
    slots = [("e", u, v) for u, v in edges] + [("q", u, n) for u in range(n)]
    for mask in range(1 << len(slots)):
        outgoing = {u: [] for u in range(n)}
        sink = [0] * n
        for i, (kind, u, v) in enumerate(slots):
            if not (mask >> i) & 1:
                continue
            if kind == "e":
                outgoing[u].append(v)
            else:
                sink[u] = 1
        if any(not outgoing[u] and not sink[u] for u in range(n)):
            continue
        reaches = [False] * n
        for u in range(n - 1, -1, -1):
            reaches[u] = bool(sink[u] or any(reaches[v] for v in outgoing[u]))
        if all(reaches):
            yield tuple(tuple(outgoing[u]) for u in range(n)), tuple(sink)


def terminal_evaluator(outgoing, sink, capacity):
    degree = tuple(len(outgoing[u]) + sink[u] for u in range(len(outgoing)))

    def legal(state, u):
        return state[u] >= degree[u] and all(state[v] < capacity[v] for v in outgoing[u])

    def fire(state, u):
        result = list(state)
        result[u] -= degree[u]
        for v in outgoing[u]:
            result[v] += 1
        return tuple(result)

    @lru_cache(maxsize=None)
    def terminals(state):
        moves = tuple(u for u in range(len(outgoing)) if legal(state, u))
        if not moves:
            return frozenset((state,))
        answer = frozenset()
        for u in moves:
            answer = answer.union(terminals(fire(state, u)))
        return answer

    return degree, terminals


def verify_positive_box(max_n: int = 4, extra_capacity: int = 1):
    counts = {"graphs": 0, "systems": 0, "initial_states": 0}
    for n in range(1, max_n + 1):
        for outgoing, sink in ordered_graphs(n):
            counts["graphs"] += 1
            degree = tuple(len(outgoing[u]) + sink[u] for u in range(n))
            capacity_ranges = [range(d, d + extra_capacity + 1) for d in degree]
            for capacity in itertools.product(*capacity_ranges):
                counts["systems"] += 1
                _, terminals = terminal_evaluator(outgoing, sink, capacity)
                for state in itertools.product(*(range(c + 1) for c in capacity)):
                    counts["initial_states"] += 1
                    found = terminals(tuple(state))
                    if len(found) != 1:
                        raise AssertionError(
                            ("nonconfluent", outgoing, sink, capacity, state, sorted(found))
                        )
    return counts


def verify_cyclic_witness():
    outgoing = ((2,), (2,), (1,))
    sink = (0, 0, 1)
    capacity = (1, 1, 2)
    initial = (1, 1, 1)
    _, terminals = terminal_evaluator(outgoing, sink, capacity)
    expected = frozenset(((0, 0, 1), (0, 1, 2)))
    found = terminals(initial)
    if found != expected:
        raise AssertionError(("cyclic witness mismatch", sorted(found), sorted(expected)))
    return {
        "outgoing": outgoing,
        "sink": sink,
        "capacity": capacity,
        "initial": initial,
        "normal_forms": sorted(found),
    }


def verify_false_normal_form_boundaries():
    # Two-vertex cycle: 0 -> 1, 1 -> 0 and sink, capacities (1, 2).
    outgoing = ((1,), (0,))
    sink = (0, 1)
    capacity = (1, 2)
    initial = (1, 2)
    degree, terminals = terminal_evaluator(outgoing, sink, capacity)
    if terminals(initial) != frozenset((initial,)):
        raise AssertionError("two-cycle state is not terminal")
    if not all(initial[u] >= degree[u] for u in range(2)):
        raise AssertionError("two-cycle terminal lost ordinary instability")

    # Parallel-edge DAG: two copies of 0 -> 1 and 1 -> sink.
    # The independent arithmetic check does not reuse the producer's weighted
    # graph representation.
    parallel_degree = (2, 1)
    parallel_capacity = (2, 1)
    parallel_initial = (2, 0)
    source_ordinary_unstable = parallel_initial[0] >= parallel_degree[0]
    source_capacity_legal = (
        source_ordinary_unstable
        and parallel_initial[1] + 2 <= parallel_capacity[1]
    )
    receiver_capacity_legal = parallel_initial[1] >= parallel_degree[1]
    if not source_ordinary_unstable or source_capacity_legal or receiver_capacity_legal:
        raise AssertionError("parallel-edge false normal form mismatch")
    return {
        "two_cycle": {
            "outgoing": outgoing,
            "sink": sink,
            "capacity": capacity,
            "initial": initial,
            "ordinary_unstable": [0, 1],
            "capacity_terminal": True,
        },
        "parallel_edge_dag": {
            "edge_multiplicity_0_to_1": 2,
            "sink": (0, 1),
            "capacity": parallel_capacity,
            "initial": parallel_initial,
            "ordinary_unstable": [0],
            "capacity_terminal": True,
        },
    }


def verify_petri_classification_witness():
    """Recompute the shared-receiver witness without producer imports."""

    outgoing = ((2,), (2,), ())
    sink = (0, 0, 1)
    capacity = (1, 1, 1)
    initial = (1, 1, 0)
    degree, terminals = terminal_evaluator(outgoing, sink, capacity)

    def legal(state, u):
        return state[u] >= degree[u] and all(
            state[v] < capacity[v] for v in outgoing[u]
        )

    def fire(state, u):
        result = list(state)
        result[u] -= degree[u]
        for v in outgoing[u]:
            result[v] += 1
        return tuple(result)

    if not legal(initial, 0) or not legal(initial, 1):
        raise AssertionError("classification witness predecessors are not enabled")
    after_zero = fire(initial, 0)
    if legal(after_zero, 1) or not legal(after_zero, 2):
        raise AssertionError("classification witness did not exhibit disabling")
    after_clear = fire(after_zero, 2)
    if not legal(after_clear, 1):
        raise AssertionError("classification witness did not exhibit re-enabling")
    found = terminals(initial)
    if found != frozenset(((0, 0, 0),)):
        raise AssertionError(("classification terminal mismatch", sorted(found)))
    return {
        "outgoing": outgoing,
        "sink": sink,
        "capacity": capacity,
        "initial": initial,
        "initially_enabled": [0, 1],
        "after_firing_0": after_zero,
        "firing_1_disabled_after_0": True,
        "after_clearing_receiver_2": after_clear,
        "firing_1_reenabled_after_clear": True,
        "normal_forms": sorted(found),
        "persistent_at_initial_marking": False,
    }


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    here = Path(__file__).resolve()
    payload = {
        "schema": "cbmd.capacity_blocked.independent_verification.v1",
        "status": "PASS",
        "positive_box": {
            "max_n": 4,
            "extra_capacity": 1,
            "simple_ordered_dags": True,
            "unit_edges": True,
            "all_states": True,
            "counts": verify_positive_box(),
        },
        "cyclic_witness": verify_cyclic_witness(),
        "false_normal_form_boundaries": verify_false_normal_form_boundaries(),
        "petri_classification_witness": verify_petri_classification_witness(),
        "verifier": {
            "path": "verification/independent_check.py",
            "sha256": sha256(here),
            "imports_reference_producer": False,
        },
    }
    args.output.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
        newline="\n",
    )


if __name__ == "__main__":
    main()

