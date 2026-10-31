"""Gated test of the checked decoder.

  * CERTIFY: random valid instances (ordered or not in the input naming, with
    sink edges, capacities at or above outdegree) are decoded in ONE Lean run;
    every instance's hypotheses must be discharged by `decide`, its `transfer`
    theorem must elaborate, and Lean's own evaluation must reconstruct the
    input exactly (edges, sink edges, capacities, and true outdegrees).
  * REFUSE: each malformed input is refused with the expected code.
  * KERNEL CONTROLS: emitting with a capacity below outdegree, or with an edge
    reversed against the order, bypassing the decoder's own validation, must be
    REJECTED BY LEAN -- otherwise the `decide` proofs would not be the
    certificate the decoder claims they are.
  * ROUND-TRIP CONTROL: a decoding that drops an edge is internally consistent,
    so Lean accepts it -- the reconstruction must reject it, or the round trip
    is idle.
  * AXIOMS: every instance theorem depends only on the allowed axioms.
"""
from __future__ import annotations

import json
import random
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from decode import Refusal, certify, emit, ns_for, parse_eval, reconstruct, run_lean, tool_path  # noqa: E402

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def random_instance(rng, n):
    names = [f"v{i}" for i in range(n)]
    rng.shuffle(names)                          # input naming need not be topological
    hidden = names[:]                           # hidden order used to generate a DAG
    edges = set()
    for i in range(n):
        for j in range(i + 1, n):
            if rng.random() < 0.4:
                edges.add((hidden[i], hidden[j]))
    for v in names:
        if rng.random() < 0.6 or not any(e[0] == v for e in edges):
            edges.add((v, "s"))
    deg = {v: sum(1 for e in edges if e[0] == v) for v in names}
    return {"vertices": names + ["s"], "sink": "s", "edges": sorted(map(list, edges)),
            "capacity": {v: deg[v] + rng.randint(0, 2) for v in names}}


BAD = {
    "CYCLE": {"vertices": ["a", "b", "s"], "sink": "s",
              "edges": [["a", "b"], ["b", "a"], ["a", "s"]], "capacity": {"a": 2, "b": 1}},
    "CAPACITY_BELOW_OUTDEGREE": {"vertices": ["a", "s"], "sink": "s",
                                 "edges": [["a", "s"]], "capacity": {"a": 0}},
    "REPEATED_EDGE": {"vertices": ["a", "b", "s"], "sink": "s",
                      "edges": [["a", "b"], ["a", "b"], ["b", "s"]], "capacity": {"a": 2, "b": 2}},
    "EDGE_OUT_OF_SINK": {"vertices": ["a", "s"], "sink": "s",
                         "edges": [["s", "a"], ["a", "s"]], "capacity": {"a": 1}},
    "LOOP": {"vertices": ["a", "s"], "sink": "s",
             "edges": [["a", "a"], ["a", "s"]], "capacity": {"a": 2}},
    "NO_OUT_EDGE": {"vertices": ["a", "b", "s"], "sink": "s",
                    "edges": [["a", "s"]], "capacity": {"a": 1, "b": 0}},
    "MISSING_CAPACITY": {"vertices": ["a", "s"], "sink": "s",
                         "edges": [["a", "s"]], "capacity": {}},
}


def run(count=60, seed=31):
    rng = random.Random(seed)
    insts, seen = [], set()
    while len(insts) < count:                   # distinct instances only
        g = random_instance(rng, rng.randint(2, 8))
        if ns_for(g) not in seen:
            seen.add(ns_for(g))
            insts.append(g)
    insts.append({"vertices": ["a", "b", "c", "s"], "sink": "s",
                  "edges": [["a", "b"], ["a", "c"], ["b", "c"], ["b", "s"], ["c", "s"]],
                  "capacity": {"a": 2, "b": 2, "c": 1}})
    srcs, orders, nss = [], [], []
    for g in insts:
        ns = ns_for(g)
        src, order = emit(g, ns)
        srcs.append(src + f"#print axioms {ns}.transfer\n")
        orders.append(order)
        nss.append(ns)
    code, out, err = run_lean("\n".join(srcs))
    lines = out.strip().splitlines()
    evals = [l for l in lines if l.startswith("DECODED|")]
    axioms_lines = " ".join(l for l in lines if not l.startswith("DECODED|"))
    used = set(re.findall(r"\b(propext|Classical\.choice|Quot\.sound|sorryAx|[A-Za-z_.]+\.ax\w*)\b",
                          axioms_lines))
    certified = 0
    if code == 0 and len(evals) == len(insts):
        for g, order, line in zip(insts, orders, evals):
            certified += certify(g, reconstruct(parse_eval(line), order, g["sink"]))
    refusals = {}
    for want, g in BAD.items():
        try:
            emit(g, "Bad")
            refusals[want] = "NOT_REFUSED"
        except Refusal as r:
            refusals[want] = r.code
    controls = {}
    for kind in ("capacity", "backward_edge"):
        g = insts[-1]
        src, _ = emit(g, "Ctl", corrupt=kind)
        c, o, e = run_lean(src)
        controls[kind] = "REJECTED_BY_LEAN" if c != 0 else "ACCEPTED"
    # round-trip control: a decoding that silently drops an edge is internally
    # consistent, so Lean accepts it; the reconstruction must reject it
    g = insts[-1]
    src, order = emit(g, "Drop", corrupt="drop_edge")
    c, o, e = run_lean(src)
    line = next((l for l in o.splitlines() if l.startswith("DECODED|")), None)
    controls["drop_edge"] = ("LEAN_ACCEPTED_ROUND_TRIP_REJECTED"
                             if c == 0 and line and not certify(g, reconstruct(parse_eval(line), order, g["sink"]))
                             else "NOT_DETECTED")
    gates = {
        "round_trip_rejects_dropped_edge": controls["drop_edge"] == "LEAN_ACCEPTED_ROUND_TRIP_REJECTED",
        "every_instance_certified": code == 0 and certified == len(insts),
        "refusals_match": all(refusals[k] == k for k in BAD),
        "lean_rejects_corrupt_capacity": controls["capacity"] == "REJECTED_BY_LEAN",
        "lean_rejects_backward_edge": controls["backward_edge"] == "REJECTED_BY_LEAN",
        "axioms_within_allowlist": used <= ALLOWED and "sorryAx" not in axioms_lines,
    }
    return {"schema": "cbmd.finite-dynamics-decoder-check.v1",
            "instances": len(insts), "certified": certified,
            "max_vertices": max(len(g["vertices"]) - 1 for g in insts),
            "lean_exit": code, "refusals": refusals, "kernel_controls": controls,
            "axioms_observed": sorted(used), "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "lean_stderr_tail": (err or "")[-800:] if code else "",
            "nonclaims": ["certifies the declared JSON format only; other graph formats need their own decoder",
                          "the decoder is trusted to emit; the kernel's decide proofs and Lean's own evaluation are the certificate"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    import os as _os

    def _available(name):
        try:
            tool_path(dict(_os.environ), name)
            return True
        except FileNotFoundError:
            return False

    if not (_available("lean") and _available("lake")):
        print(json.dumps({"status": "TOOLCHAIN_UNAVAILABLE",
                          "detail": "set CBMD_LEAN_BIN to the pinned Lean 4.35.0 bin directory or put lean and lake on PATH",
                          "authority_effect": "NONE"}))
        raise SystemExit(3)
    out = run()
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
