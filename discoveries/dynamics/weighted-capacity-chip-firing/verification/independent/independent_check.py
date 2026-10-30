"""Independent check of the weighted transfer theorem's CONCLUSION.

Written separately from search_v2.py and testing a different statement: not
"the capacity system has one normal form", but

    every capacity-terminal state reachable from x equals the ORDINARY
    (uncapacitated) normal form of x,

which is what `CBMDWeightedDynamics.weighted_transfer` asserts.  The ordinary
normal form is computed by unconstrained greedy firing, a separate dynamic from
the capacity-blocked search.  Adverse controls are included: the same test is
run at a capacity one below the bound, where it must FAIL.
"""
from __future__ import annotations
import json, sys
from itertools import product


def od(a, s, u):
    return s[u] + sum(a[u])


def ordinary_normal(a, s, n, x):
    """Uncapacitated stabilization by greedy firing. Terminates on an ordered DAG."""
    y = list(x)
    guard = 0
    while True:
        for u in range(n):
            if y[u] >= od(a, s, u):
                y[u] -= od(a, s, u)
                for v in range(n):
                    y[v] += a[u][v]
                break
        else:
            return tuple(y)
        guard += 1
        if guard > 10 ** 6:
            raise RuntimeError("ordinary firing did not terminate")


def cap_terminals(a, s, c, n, x):
    """All capacity-terminal states reachable from x, by explicit DFS over the
    capacity-legal relation (iterative, distinct from the BFS in search_v2)."""
    stack = [tuple(x)]
    seen = {tuple(x)}
    out = set()
    while stack:
        y = stack.pop()
        moved = False
        for u in range(n):
            if y[u] < od(a, s, u):
                continue
            if any(y[v] + a[u][v] > c[v] for v in range(n)):
                continue
            moved = True
            z = list(y)
            z[u] -= od(a, s, u)
            for v in range(n):
                z[v] += a[u][v]
            z = tuple(z)
            if z not in seen:
                seen.add(z)
                stack.append(z)
        if not moved:
            out.add(y)
    return out


def graphs(n, mm, ms):
    slots = [(u, v) for u in range(n) for v in range(u + 1, n)]
    for ev in product(range(mm + 1), repeat=len(slots)):
        for sv in product(range(ms + 1), repeat=n):
            a = [[0] * n for _ in range(n)]
            for val, (u, v) in zip(ev, slots):
                a[u][v] = val
            if any(od(a, sv, u) == 0 for u in range(n)):
                continue
            r = [False] * n
            for u in range(n - 1, -1, -1):
                r[u] = sv[u] > 0 or any(a[u][v] > 0 and r[v] for v in range(u + 1, n))
            if not all(r):
                continue
            yield tuple(tuple(z) for z in a), tuple(sv)


def maxin(a, n, v):
    return max((a[u][v] for u in range(n)), default=0)


def check(max_n, mm, ms, lower_at_receiver=False):
    agree = disagree = systems = states = 0
    first_bad = None
    for n in range(1, max_n + 1):
        for a, s in graphs(n, mm, ms):
            base = [od(a, s, v) + max(0, maxin(a, n, v) - 1) for v in range(n)]
            targets = [None]
            if lower_at_receiver:
                targets = [t for t in range(n) if maxin(a, n, t) >= 2]
            for t in targets:
                c = list(base)
                if t is not None:
                    c[t] -= 1
                    if c[t] < od(a, s, t):
                        continue
                systems += 1
                for x in product(*(range(ci + 1) for ci in c)):
                    states += 1
                    onf = ordinary_normal(a, s, n, x)
                    for term in cap_terminals(a, s, tuple(c), n, x):
                        if term == onf:
                            agree += 1
                        else:
                            disagree += 1
                            if first_bad is None:
                                first_bad = {"arcs": [list(r) for r in a], "sink": list(s),
                                             "capacity": c, "initial": list(x),
                                             "capacity_terminal": list(term),
                                             "ordinary_normal": list(onf),
                                             "lowered_at": t}
    return {"systems": systems, "initial_states": states, "terminal_agreements": agree,
            "terminal_disagreements": disagree, "first_disagreement": first_bad}


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    mm = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    ms = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    out = {"schema": "cbmd.weighted-transfer-independent-check.v1",
           "box": {"max_n": n, "max_multiplicity": mm, "max_sink_multiplicity": ms},
           "at_bound": check(n, mm, ms, lower_at_receiver=False),
           "adverse_control_one_below_at_one_receiver": check(n, mm, ms, lower_at_receiver=True)}
    out["status"] = ("PASS" if out["at_bound"]["terminal_disagreements"] == 0
                     and out["adverse_control_one_below_at_one_receiver"]["terminal_disagreements"] > 0
                     else "FAIL")
    print(json.dumps(out, indent=1))
    sys.exit(0 if out["status"] == "PASS" else 1)
