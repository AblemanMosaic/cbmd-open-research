"""Can ANY capacity rescue a cyclic graph?

Conjecture C: if the nonsink arc relation has a directed cycle and C(v) >= d(v) on it,
then the state filling every cycle vertex to capacity is capacity-terminal but not
ordinarily stable -- so transfer fails at EVERY capacity meeting the natural threshold,
and no enlargement helps.

Tested by brute force over small cyclic digraphs and a wide capacity sweep.
"""
from __future__ import annotations
import json
from itertools import product


def od(a, s, u): return s[u] + sum(a[u])


def ordinary_normal(a, s, n, x, guard=10**6):
    y = list(x); steps = 0
    while True:
        for u in range(n):
            if y[u] >= od(a, s, u):
                y[u] -= od(a, s, u)
                for v in range(n): y[v] += a[u][v]
                break
        else:
            return tuple(y)
        steps += 1
        if steps > guard: return None          # ordinary firing need not terminate on a cycle


def cap_terminal(a, s, c, n, x):
    return all(x[u] < od(a, s, u) or any(x[v] + a[u][v] > c[v] for v in range(n))
               for u in range(n))


def ordinarily_stable(a, s, n, x):
    return all(x[u] < od(a, s, u) for u in range(n))


def has_cycle(a, n):
    """Directed cycle among nonsink vertices?"""
    colour = [0] * n
    def dfs(u):
        colour[u] = 1
        for v in range(n):
            if a[u][v] > 0:
                if colour[v] == 1: return True
                if colour[v] == 0 and dfs(v): return True
        colour[u] = 2
        return False
    return any(colour[u] == 0 and dfs(u) for u in range(n))


def cycle_vertices(a, n):
    """Vertices lying on some directed cycle (nonsink arcs)."""
    reach = [[a[u][v] > 0 for v in range(n)] for u in range(n)]
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if reach[i][k] and reach[k][j]: reach[i][j] = True
    return [u for u in range(n) if reach[u][u]]


def digraphs(n, mm, ms):
    slots = [(u, v) for u in range(n) for v in range(n) if u != v]
    for ev in product(range(mm + 1), repeat=len(slots)):
        for sv in product(range(ms + 1), repeat=n):
            a = [[0] * n for _ in range(n)]
            for val, (u, v) in zip(ev, slots): a[u][v] = val
            if any(od(a, sv, u) == 0 for u in range(n)): continue
            # every nonsink vertex reaches the sink
            r = [sv[u] > 0 for u in range(n)]
            changed = True
            while changed:
                changed = False
                for u in range(n):
                    if not r[u] and any(a[u][v] > 0 and r[v] for v in range(n)):
                        r[u] = True; changed = True
            if not all(r): continue
            yield tuple(tuple(z) for z in a), tuple(sv)


def run(n_max=3, mm=2, ms=1, slack_max=6):
    """For each cyclic graph, test the predicted witness at capacity d+slack for slack=0..slack_max."""
    rows = []
    confirmed = refuted = 0
    for n in range(2, n_max + 1):
        for a, s in digraphs(n, mm, ms):
            if not has_cycle(a, n): continue
            cyc = cycle_vertices(a, n)
            for slack in range(slack_max + 1):
                c = tuple(od(a, s, v) + slack for v in range(n))
                # predicted witness: cycle vertices full, others empty
                x = tuple(c[v] if v in cyc else 0 for v in range(n))
                term = cap_terminal(a, s, c, n, x)
                stable = ordinarily_stable(a, s, n, x)
                if term and not stable:
                    confirmed += 1
                else:
                    refuted += 1
                    if len(rows) < 5:
                        rows.append({"arcs": [list(r) for r in a], "sink": list(s), "slack": slack,
                                     "capacity": list(c), "witness": list(x),
                                     "capacity_terminal": term, "ordinarily_stable": stable})
    return {"confirmed": confirmed, "refuted": refuted, "refutation_samples": rows}


def exhaustive_all_states(n_max=3, mm=2, ms=1, slack_max=4):
    """Stronger: over ALL states, does transfer ever hold for a cyclic graph at any slack?"""
    out = []
    for n in range(2, n_max + 1):
        for a, s in digraphs(n, mm, ms):
            if not has_cycle(a, n): continue
            for slack in range(slack_max + 1):
                c = tuple(od(a, s, v) + slack for v in range(n))
                bad = None
                for x in product(*(range(ci + 1) for ci in c)):
                    if cap_terminal(a, s, c, n, x) and not ordinarily_stable(a, s, n, x):
                        bad = list(x); break
                if bad is None:
                    out.append({"arcs": [list(r) for r in a], "sink": list(s),
                                "slack": slack, "capacity": list(c),
                                "note": "no false terminal found at this capacity"})
    return out


if __name__ == "__main__":
    r = {"schema": "cbmd.cycle-obstruction-probe.v1",
         "predicted_witness": run(),
         "cyclic_systems_with_no_false_terminal": exhaustive_all_states()}
    print(json.dumps(r, indent=1))
