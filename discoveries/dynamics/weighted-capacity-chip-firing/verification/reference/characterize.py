"""Which (graph, capacity) pairs preserve the ordinary normal form?

Sufficiency is known (forward-ordered arcs + d(v)+b(v) <= C(v)+1) and the ordering
is necessary (cycle obstruction). Neither gives a CHARACTERIZATION over arbitrary
digraphs and arbitrary capacities. This tabulates the exact predicate

    TRANSFER(G, C)  <=>  for every admissible x, every capacity-terminal state
                         reachable from x equals the ordinary normal form of x

exhaustively on small systems, then tests candidate characterizations against it.

Note: with no capacity, firing on a cyclic graph may not terminate; every vertex
reaches the sink, which makes ordinary firing terminate because total chips
strictly decrease whenever a sink arc fires. A guard is kept anyway and any
non-terminating case is excluded and counted.
"""
from __future__ import annotations

import json
from itertools import product


def od(a, s, u): return s[u] + sum(a[u])


def ordinary_normal(a, s, n, x, guard=200000):
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
        if steps > guard: return None


def legal(a, s, c, n, x, u):
    return x[u] >= od(a, s, u) and all(x[v] + a[u][v] <= c[v] for v in range(n))


def cap_terminals(a, s, c, n, x, cap=200000):
    stack = [tuple(x)]; seen = {tuple(x)}; out = set()
    while stack:
        y = stack.pop(); moved = False
        for u in range(n):
            if not legal(a, s, c, n, y, u): continue
            moved = True
            z = list(y); z[u] -= od(a, s, u)
            for v in range(n): z[v] += a[u][v]
            z = tuple(z)
            if z not in seen:
                if len(seen) > cap: return None
                seen.add(z); stack.append(z)
        if not moved: out.add(y)
    return out


def transfer_holds(a, s, c, n):
    for x in product(*(range(ci + 1) for ci in c)):
        onf = ordinary_normal(a, s, n, x)
        if onf is None: return None
        terms = cap_terminals(a, s, c, n, x)
        if terms is None: return None
        if terms != {onf}: return False
    return True


def digraphs(n, mm, ms):
    slots = [(u, v) for u in range(n) for v in range(n) if u != v]
    for ev in product(range(mm + 1), repeat=len(slots)):
        for sv in product(range(ms + 1), repeat=n):
            a = [[0] * n for _ in range(n)]
            for val, (u, v) in zip(ev, slots): a[u][v] = val
            if any(od(a, sv, u) == 0 for u in range(n)): continue
            r = [sv[u] > 0 for u in range(n)]
            ch = True
            while ch:
                ch = False
                for u in range(n):
                    if not r[u] and any(a[u][v] > 0 and r[v] for v in range(n)):
                        r[u] = True; ch = True
            if not all(r): continue
            yield tuple(tuple(z) for z in a), tuple(sv)


# ---------------- candidate predicates ----------------
def live(a, s, c, n):
    """Vertices that can ever hold enough chips to fire under the capacity box."""
    return [v for v in range(n) if c[v] >= od(a, s, v)]


def acyclic_on(a, n, vs):
    colour = {v: 0 for v in vs}
    def dfs(u):
        colour[u] = 1
        for v in vs:
            if a[u][v] > 0:
                if colour[v] == 1: return True
                if colour[v] == 0 and dfs(v): return True
        colour[u] = 2; return False
    return not any(colour[v] == 0 and dfs(v) for v in vs)


def bound_on_live(a, s, c, n, L):
    """C(v) >= d(v) + max_{u in L} m(u,v) - 1 for every v in L receiving from L."""
    for v in L:
        mx = max((a[u][v] for u in L if a[u][v] > 0), default=0)
        if mx and c[v] + 1 < od(a, s, v) + mx: return False
    return True


def no_live_to_dead(a, c, n, L):
    """No live vertex sends to a vertex outside L."""
    dead = [v for v in range(n) if v not in L]
    return all(a[u][v] == 0 for u in L for v in dead)


def candidate_characterization(a, s, c, n):
    L = live(a, s, c, n)
    if not L: return True                       # nothing can ever fire
    return acyclic_on(a, n, L) and bound_on_live(a, s, c, n, L) and no_live_to_dead(a, c, n, L)


def run(n_max=3, mm=2, ms=1, slack=2):
    rows = {"schema": "cbmd.transfer-characterization.v1",
            "box": {"n_max": n_max, "max_multiplicity": mm, "max_sink_multiplicity": ms,
                    "capacity_range": f"0..d(v)+{slack}"}}
    tt = tf = ft = ff = skipped = 0
    false_pos = []     # predicate says yes, transfer is false  -> predicate UNSOUND
    false_neg = []     # predicate says no, transfer is true    -> predicate INCOMPLETE
    for n in range(1, n_max + 1):
        for a, s in digraphs(n, mm, ms):
            for c in product(*(range(od(a, s, v) + slack + 1) for v in range(n))):
                actual = transfer_holds(a, s, tuple(c), n)
                if actual is None: skipped += 1; continue
                pred = candidate_characterization(a, s, tuple(c), n)
                if pred and actual: tt += 1
                elif pred and not actual:
                    tf += 1
                    if len(false_pos) < 6:
                        false_pos.append({"arcs": [list(r) for r in a], "sink": list(s),
                                          "capacity": list(c), "outdeg": [od(a, s, v) for v in range(n)],
                                          "live": live(a, s, tuple(c), n)})
                elif not pred and actual:
                    ft += 1
                    if len(false_neg) < 6:
                        false_neg.append({"arcs": [list(r) for r in a], "sink": list(s),
                                          "capacity": list(c), "outdeg": [od(a, s, v) for v in range(n)],
                                          "live": live(a, s, tuple(c), n)})
                else: ff += 1
    rows["confusion"] = {"predicate_and_transfer": tt, "predicate_not_transfer_UNSOUND": tf,
                         "transfer_not_predicate_INCOMPLETE": ft, "neither": ff, "skipped": skipped}
    rows["unsound_samples"] = false_pos
    rows["incomplete_samples"] = false_neg
    rows["exact"] = (tf == 0 and ft == 0)
    return rows


if __name__ == "__main__":
    print(json.dumps(run(), indent=1))
