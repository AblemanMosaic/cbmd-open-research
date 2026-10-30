"""A capacitated sink collapses transfer (revision 0.7.0).

Every theorem in this dossier assumes an absorbing sink.  Here the capacity
model also caps the sink at `sinkcap`, while ordinary firing keeps the
absorbing sink (so ordinary normal forms still exist).  Lean
(`SinkCollapse.lean`) proves:

  capped_sink_breaks_transfer   Sends /\\ Live v  ->  the all-full state is
                                admissible, capacity-terminal, not stable
  no_live_all_stable            no vertex live    ->  every admissible state
                                is ordinarily stable

so the predicted census statement is

    TRANSFER (capped sink)  <=>  no vertex is live,   at EVERY finite sinkcap.

Content gates (a pass requires all of them):

  * exact agreement, 0 disagreements, at every tested sink capacity;
  * BOTH populations non-empty (systems with a live vertex, and without);
  * BRIDGE: the Lean hypothesis `Sends` holds of every generated system;
  * WITNESS: for every live system and sink capacity, the all-full state is
    checked directly to be capacity-terminal and not ordinarily stable --
    the Lean conclusion itself, not only its consequence for transfer;
  * NON-VACUITY: some systems transfer with the ABSORBING sink and fail at
    every finite cap.  If none did, the collapse would only be restating
    failures the absorbing theory already had, and the cap would be idle.

Standard library only.  Usage:  sink_collapse.py [n_max]
"""
from __future__ import annotations

import json
import sys
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from characterize import digraphs, od, ordinary_normal, transfer_holds  # noqa: E402

SINKCAPS = (0, 1, 2, 4)


def legal(a, s, c, sc, n, x, k, u):
    if x[u] < od(a, s, u):
        return False
    if any(x[v] + a[u][v] > c[v] for v in range(n)):
        return False
    return k + s[u] <= sc


def terminals(a, s, c, sc, n, x0, k0):
    start = (tuple(x0), k0)
    stack, seen, out = [start], {start}, set()
    while stack:
        x, k = stack.pop()
        moved = False
        for u in range(n):
            if not legal(a, s, c, sc, n, x, k, u):
                continue
            moved = True
            z = list(x)
            z[u] -= od(a, s, u)
            for v in range(n):
                z[v] += a[u][v]
            st = (tuple(z), k + s[u])
            if st not in seen:
                seen.add(st)
                stack.append(st)
        if not moved:
            out.add(x)
    return out


def capped_transfer(a, s, c, sc, n):
    for x in product(*(range(ci + 1) for ci in c)):
        onf = ordinary_normal(a, s, n, x)
        for k in range(sc + 1):
            if terminals(a, s, c, sc, n, x, k) != {onf}:
                return False
    return True


def run(n_max=3, mm=2, ms=1, slack=1):
    agree = disagree = live_sys = dead_sys = 0
    bridge_fail = witness_fail = absorbing_only = 0
    samples = []
    for n in range(1, n_max + 1):
        for a, s in digraphs(n, mm, ms):
            if not all(s[v] > 0 or any(a[v][w] > 0 for w in range(n)) for v in range(n)):
                bridge_fail += 1
            for c in product(*(range(od(a, s, v) + slack + 1) for v in range(n))):
                live = any(c[v] >= od(a, s, v) for v in range(n))
                live_sys += live
                dead_sys += not live
                fails_everywhere = True
                for sc in SINKCAPS:
                    if live:
                        full = tuple(c)
                        terminal = not any(legal(a, s, c, sc, n, full, sc, u) for u in range(n))
                        unstable = any(full[v] >= od(a, s, v) for v in range(n))
                        if not (terminal and unstable):
                            witness_fail += 1
                    t = capped_transfer(a, s, c, sc, n)
                    fails_everywhere &= not t
                    if t == (not live):
                        agree += 1
                    else:
                        disagree += 1
                        if len(samples) < 4:
                            samples.append({"arcs": [list(r) for r in a], "sink": list(s),
                                            "cap": list(c), "sinkcap": sc, "transfer": t})
                if live and fails_everywhere and transfer_holds(a, s, c, n):
                    absorbing_only += 1
    gates = {
        "zero_disagreements": disagree == 0 and agree > 0,
        "live_population_nonempty": live_sys > 0,
        "dead_population_nonempty": dead_sys > 0,
        "bridge_sends_holds": bridge_fail == 0,
        "allfull_witness_checked": witness_fail == 0,
        "cap_not_idle": absorbing_only > 0,
    }
    return {
        "schema": "cbmd.weighted-sink-collapse.v1",
        "box": {"n_max": n_max, "max_mult": mm, "max_sink_mult": ms,
                "capacity_slack": slack, "sink_capacities": list(SINKCAPS)},
        "agree": agree, "disagree": disagree,
        "systems_with_live_vertex": live_sys, "systems_all_dead": dead_sys,
        "bridge_failures": bridge_fail, "witness_failures": witness_fail,
        "transfer_absorbing_but_fails_every_cap": absorbing_only,
        "disagreement_samples": samples,
        "gates": gates,
        "status": "PASS" if all(gates.values()) else "FAIL",
        "nonclaims": ["finite census over the stated box; corroborates the Lean theorems, does not prove them"],
    }


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 3)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
