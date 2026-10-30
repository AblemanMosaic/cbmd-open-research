"""Weighted capacity-blocked chip-firing, v2.

v1 defect (recorded): lowering the bound at EVERY vertex also lowers it at sources, where
C(u) < d(u) freezes u forever. That regime is degenerate and reports no nonconfluence for
the wrong reason. v2 lowers capacity one receiver at a time and first reproduces the
repository's known adverse witness as a positive control.
"""
from __future__ import annotations
import json, sys
from itertools import product
from collections import deque

def outdeg(a, s, u): return s[u] + sum(a[u])
def maxin(a, n, v): return max((a[u][v] for u in range(n)), default=0)

def legal(a, s, c, n, x, u):
    return x[u] >= outdeg(a, s, u) and all(x[v] + a[u][v] <= c[v] for v in range(n))

def fire(a, s, n, x, u):
    y = list(x); y[u] -= outdeg(a, s, u)
    for v in range(n): y[v] += a[u][v]
    return tuple(y)

def normal_forms(a, s, c, n, start):
    seen = {start}; todo = deque([start]); nfs = set()
    while todo:
        x = todo.popleft(); fired = False
        for u in range(n):
            if legal(a, s, c, n, x, u):
                fired = True; y = fire(a, s, n, x, u)
                if y not in seen: seen.add(y); todo.append(y)
        if not fired: nfs.add(x)
    return nfs, len(seen)

def nonconfluent_witness(a, s, c, n):
    """First initial state (lexicographic) with two normal forms, else None."""
    for start in product(*(range(ci + 1) for ci in c)):
        nfs, reach = normal_forms(a, s, c, n, start)
        if len(nfs) > 1:
            return {"initial": list(start), "normal_forms": sorted(list(x) for x in nfs), "reachable": reach}
    return None

def graphs(n, maxmult, maxsink):
    slots = [(u, v) for u in range(n) for v in range(u + 1, n)]
    for ev in product(range(maxmult + 1), repeat=len(slots)):
        for sv in product(range(maxsink + 1), repeat=n):
            a = [[0] * n for _ in range(n)]
            for val, (u, v) in zip(ev, slots): a[u][v] = val
            if any(outdeg(a, sv, u) == 0 for u in range(n)): continue
            reach = [False] * n
            for u in range(n - 1, -1, -1):
                reach[u] = sv[u] > 0 or any(a[u][v] > 0 and reach[v] for v in range(u + 1, n))
            if not all(reach): continue
            yield tuple(tuple(r) for r in a), tuple(sv)

def desc(a, s, c, n, w):
    return {"n": n, "arcs": [list(r) for r in a], "sink": list(s),
            "outdeg": [outdeg(a, s, u) for u in range(n)],
            "maxin": [maxin(a, n, v) for v in range(n)],
            "capacity": list(c), **w}

def ordinary_normal(a, s, n, x):
    """Uncapacitated stabilization (greedy); terminates on an ordered DAG."""
    y = list(x)
    while True:
        for u in range(n):
            if y[u] >= outdeg(a, s, u):
                y[u] -= outdeg(a, s, u)
                for v in range(n):
                    y[v] += a[u][v]
                break
        else:
            return tuple(y)


def transfer_fails(a, s, c, n):
    """First initial state whose capacity-terminal set is not {ordinary normal form}.

    This is the property the theorem is about. It is STRICTLY STRONGER than
    nonconfluence: a capacity system can have a unique normal form that is still
    not the ordinary one (premature termination). The smallest such witness has
    two vertices and is invisible to a confluence-only search.
    """
    for start in product(*(range(ci + 1) for ci in c)):
        onf = ordinary_normal(a, s, n, start)
        nfs, _ = normal_forms(a, s, c, n, start)
        if nfs != {onf}:
            return {"initial": list(start), "ordinary_normal": list(onf),
                    "capacity_terminals": sorted(list(z) for z in nfs),
                    "distinct_normal_forms": len(nfs)}
    return None


def run(max_n=4, maxmult=3, maxsink=2, extra=1, cap_limit=400000):
    out = {"schema": "cbmd.weighted-chipfiring-search.v3"}
    # --- positive control: the unit-edge bound C(v) >= d(v) applied to weighted graphs
    ctrl = []; ctrl_stats = {"graphs": 0, "systems": 0}
    for n in range(1, max_n + 1):
        for a, s in graphs(n, maxmult, maxsink):
            ctrl_stats["graphs"] += 1
            c = tuple(outdeg(a, s, v) for v in range(n))
            ctrl_stats["systems"] += 1
            w = nonconfluent_witness(a, s, c, n)
            if w: ctrl.append(desc(a, s, c, n, w))
    # transfer-failure control at C=d: the property the theorem asserts
    tctrl = []
    for n in range(1, max_n + 1):
        for a, s in graphs(n, maxmult, maxsink):
            c = tuple(outdeg(a, s, v) for v in range(n))
            w = transfer_fails(a, s, c, n)
            if w:
                tctrl.append(desc(a, s, c, n, w))
    out["transfer_control_C_eq_d"] = {
        "note": "systems at C=d whose capacity-terminal set is not the ordinary normal form; strictly more sensitive than nonconfluence",
        "failing_systems": len(tctrl),
        "smallest": sorted(tctrl, key=lambda r: (r["n"], sum(map(sum, r["arcs"])) + sum(r["sink"]), sum(r["capacity"]), r["arcs"], r["sink"]))[:3]}
    out["positive_control_C_eq_d"] = {"stats": ctrl_stats, "nonconfluent_systems": len(ctrl),
                                      "smallest": sorted(ctrl, key=lambda r: (r["n"], sum(map(sum, r["arcs"])) + sum(r["sink"]), sum(r["capacity"]), r["arcs"], r["sink"]))[:3]}
    # --- candidate bound C(v) >= d(v) + max(0, maxin(v)-1), capacities bound..bound+extra
    cand = []; cstats = {"graphs": 0, "systems": 0, "initials_skipped": 0}
    for n in range(1, max_n + 1):
        for a, s in graphs(n, maxmult, maxsink):
            cstats["graphs"] += 1
            base = [outdeg(a, s, v) + max(0, maxin(a, n, v) - 1) for v in range(n)]
            for c in product(*(range(base[v], base[v] + extra + 1) for v in range(n))):
                size = 1
                for ci in c: size *= ci + 1
                if size > cap_limit: cstats["initials_skipped"] += 1; continue
                cstats["systems"] += 1
                w = nonconfluent_witness(a, s, tuple(c), n)
                if w: cand.append(desc(a, s, tuple(c), n, w))
    out["candidate_bound"] = {"formula": "C(v) >= d(v) + max(0, max_u m(u,v) - 1)", "stats": cstats,
                              "nonconfluent_systems": len(cand), "witnesses": cand[:5]}
    # --- sharpness: lower capacity by one at a SINGLE receiver with maxin >= 2, others at bound
    sharp = []; sstats = {"systems": 0}
    for n in range(1, max_n + 1):
        for a, s in graphs(n, maxmult, maxsink):
            base = [outdeg(a, s, v) + max(0, maxin(a, n, v) - 1) for v in range(n)]
            for t in range(n):
                if maxin(a, n, t) < 2: continue
                c = list(base); c[t] -= 1
                if c[t] < outdeg(a, s, t): continue   # keep t able to fire; isolate the receiver effect
                size = 1
                for ci in c: size *= ci + 1
                if size > cap_limit: continue
                sstats["systems"] += 1
                w = nonconfluent_witness(a, s, tuple(c), n)
                if w: sharp.append({**desc(a, s, tuple(c), n, w), "lowered_at": t})
    # sharpness in the transfer sense, one receiver lowered
    tsharp = []
    for n in range(1, max_n + 1):
        for a, s in graphs(n, maxmult, maxsink):
            base = [outdeg(a, s, v) + max(0, maxin(a, n, v) - 1) for v in range(n)]
            for t in range(n):
                if maxin(a, n, t) < 2: continue
                c = list(base); c[t] -= 1
                if c[t] < outdeg(a, s, t): continue
                w = transfer_fails(a, s, tuple(c), n)
                if w: tsharp.append({**desc(a, s, tuple(c), n, w), "lowered_at": t})
    out["transfer_sharpness_one_receiver_lowered"] = {
        "failing_systems": len(tsharp),
        "smallest": sorted(tsharp, key=lambda r: (r["n"], sum(map(sum, r["arcs"])) + sum(r["sink"]), sum(r["capacity"]), r["arcs"], r["sink"]))[:3]}
    out["sharpness_one_receiver_lowered"] = {"stats": sstats, "nonconfluent_systems": len(sharp),
                                             "smallest": sorted(sharp, key=lambda r: (r["n"], sum(map(sum, r["arcs"])) + sum(r["sink"]), sum(r["capacity"]), r["arcs"], r["sink"]))[:3]}
    return out

if __name__ == "__main__":
    import argparse
    p = argparse.ArgumentParser(); p.add_argument("--n", type=int, default=3); p.add_argument("--mult", type=int, default=3)
    p.add_argument("--sink", type=int, default=2); p.add_argument("--extra", type=int, default=1)
    a = p.parse_args()
    r = run(max_n=a.n, maxmult=a.mult, maxsink=a.sink, extra=a.extra)
    r["box"] = {"max_n": a.n, "max_multiplicity": a.mult, "max_sink_multiplicity": a.sink, "capacity_extra": a.extra}
    print(json.dumps(r, indent=1))
