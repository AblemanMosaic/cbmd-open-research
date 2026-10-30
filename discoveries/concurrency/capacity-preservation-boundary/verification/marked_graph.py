"""Marked graphs are polynomial (revision 0.11.0).

Revision 0.10.0 showed free choice does not help.  This is the other side:
in a MARKED GRAPH -- every place has at most one consuming transition and at
most one producing transition, self-loops allowed -- preservation is decidable
in polynomial time, for ARBITRARY weights and capacities (written in binary).

## Why

A transition t is capacity-blocked exactly when one of its literals holds:

    m(q) <= pre(t,q) - 1                       for each input q of t      (le)
    m(q) >= cap(q) - post(t,q) + pre(t,q) + 1  for each q with post > pre  (ge)

In a marked graph each place q carries at most one `le` literal (its consumer)
and at most one `ge` literal (its producer): every variable occurs in at most
two clauses.  A bad marking is an admissible marking with every transition
blocked and some t0 ordinarily enabled.  Fix t0 (T choices); ordinary
enabledness of t0 raises the domain floor of its inputs to pre(t0,q).  Then:

  * a literal unsatisfiable in its domain is dropped;
  * a place with one surviving literal satisfies that clause outright;
  * a place whose two literals are JOINTLY satisfiable (or which sits on a
    self-loop) satisfies both clauses outright -- it occurs nowhere else;
  * a place whose two literals are mutually exclusive is an EDGE between its
    two clauses: any value satisfies at most one, and some value satisfies
    either.

The remaining question is whether the edges can be oriented so that every
unsatisfied clause receives one.  A connected component can be so oriented iff
it contains an already-satisfied clause or has at least as many edges as
vertices (Hakimi-style orientation; a spanning tree out of the root, or a cycle
with trees hanging off it).  So the whole decision is T union-find passes.

This is the classical fact that SAT with every variable occurring at most
twice is polynomial, adapted to threshold literals.  It is a WRITTEN argument;
nothing here is compiled.

## Gates

  * agreement with an independent brute-force search over all admissible
    markings, using this dossier's `petri.capacity_enabled`;
  * both outcomes occur, and nets with a multi-input transition occur and
    include non-preserving ones -- otherwise the polynomial side would be the
    already-known single-input case;
  * every generated net is checked to be a marked graph, and the checker is
    shown to reject the revision 0.10.0 free-choice nets (control);
  * ABLATION `no_t0_floor`: dropping the domain floor from t0 must give wrong
    verdicts;
  * ABLATION `edges_satisfy_both`: treating an exclusive pair as satisfying
    both clauses (i.e. ignoring the orientation count) must give wrong verdicts.
"""
from __future__ import annotations

import json
import os
import random
import sys
from itertools import product

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from petri import capacity_enabled, ordinarily_enabled  # noqa: E402


def brute(pre, post, cap, P, T):
    for m in product(*(range(c + 1) for c in cap)):
        if all(not capacity_enabled(pre, post, cap, m, t, P) for t in range(T)) and \
                any(ordinarily_enabled(pre, m, t, P) for t in range(T)):
            return False
    return True


def is_marked_graph(pre, post, P, T):
    return all(sum(1 for t in range(T) if pre[t][q] > 0) <= 1 and
               sum(1 for t in range(T) if post[t][q] > 0) <= 1 for q in range(P))


def literals(pre, post, cap, P, T):
    L = [[] for _ in range(T)]
    for t in range(T):
        for q in range(P):
            if pre[t][q] > 0:
                L[t].append((q, "le", pre[t][q] - 1))
            if post[t][q] > pre[t][q]:
                L[t].append((q, "ge", cap[q] - post[t][q] + pre[t][q] + 1))
    return L


def _sat(lit, lo, hi):
    _q, kind, b = lit
    return lo <= min(b, hi) if kind == "le" else max(b, lo) <= hi


def bad_with(pre, post, cap, P, T, t0, ablate=None):
    lo = [0] * P if ablate == "no_t0_floor" else [pre[t0][q] for q in range(P)]
    hi = list(cap)
    if any(lo[q] > hi[q] for q in range(P)):
        return False
    occ: dict[int, list] = {}
    for t, lits in enumerate(literals(pre, post, cap, P, T)):
        for lit in lits:
            if _sat(lit, lo[lit[0]], hi[lit[0]]):
                occ.setdefault(lit[0], []).append((t, lit))
    satisfied, edges = set(), []
    for q, lst in occ.items():
        if len(lst) == 1:
            satisfied.add(lst[0][0])
            continue
        (t1, l1), (t2, l2) = lst
        if ablate == "edges_satisfy_both":
            satisfied |= {t1, t2}
            continue
        lo2, hi2 = lo[q], hi[q]
        for l in (l1, l2):
            if l[1] == "le":
                hi2 = min(hi2, l[2])
            else:
                lo2 = max(lo2, l[2])
        if lo2 <= hi2 or t1 == t2:
            satisfied |= {t1, t2}
        else:
            edges.append((t1, t2))
    parent = list(range(T))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    for a, b in edges:
        parent[find(a)] = find(b)
    comp: dict[int, list] = {}
    for t in range(T):
        c = comp.setdefault(find(t), [0, 0, False])
        c[0] += 1
        c[2] |= t in satisfied
    for a, _b in edges:
        comp[find(a)][1] += 1
    return all(c[2] or c[1] >= c[0] for c in comp.values())


def decide(pre, post, cap, P, T, ablate=None):
    """True iff the net preserves."""
    return not any(bad_with(pre, post, cap, P, T, t0, ablate) for t0 in range(T))


def random_marked_graph(rng, P, T, w, capmax):
    pre = [[0] * P for _ in range(T)]
    post = [[0] * P for _ in range(T)]
    for q in range(P):
        c, p = rng.randrange(T + 1), rng.randrange(T + 1)      # T means none
        if c < T:
            pre[c][q] = rng.randint(1, w)
        if p < T:
            post[p][q] = rng.randint(1, w)
    return pre, post, [rng.randint(0, capmax) for _ in range(P)]


def run(trials=20000, seed=11):
    rng = random.Random(seed)
    agree = disagree = pres = nonpres = multi = multi_np = not_mg = 0
    abl = {"no_t0_floor": 0, "edges_satisfy_both": 0}
    samples = []
    for _ in range(trials):
        P, T = rng.randint(1, 4), rng.randint(1, 4)
        pre, post, cap = random_marked_graph(rng, P, T, rng.choice([1, 2, 3]),
                                             rng.choice([1, 2, 3]))
        not_mg += not is_marked_graph(pre, post, P, T)
        truth = brute(pre, post, cap, P, T)
        verdict = decide(pre, post, cap, P, T)
        pres += truth
        nonpres += not truth
        if any(sum(1 for q in range(P) if pre[t][q]) >= 2 for t in range(T)):
            multi += 1
            multi_np += not truth
        if verdict == truth:
            agree += 1
        else:
            disagree += 1
            if len(samples) < 3:
                samples.append({"pre": pre, "post": post, "cap": cap, "preserves": truth})
        for a in abl:
            abl[a] += decide(pre, post, cap, P, T, a) != truth
    # Control on the marked-graph checker: the revision 0.10.0 free-choice nets
    # are not marked graphs (g has many consumers) and must be rejected.
    from free_choice import fc_net, population
    rejected = sum(not is_marked_graph(*(lambda r: (r[0], r[1], r[3], r[4]))(fc_net(n, cnf)))
                   for n, cnf in population(20))
    gates = {
        "marked_graph_check_rejects_free_choice_nets": rejected > 0,
        "procedure_is_exact": disagree == 0 and agree > 0,
        "both_outcomes_occur": pres > 0 and nonpres > 0,
        "multi_input_population_nonempty": multi > 0 and multi_np > 0,
        "every_net_is_a_marked_graph": not_mg == 0,
        "ablation_no_t0_floor_breaks": abl["no_t0_floor"] > 0,
        "ablation_edges_satisfy_both_breaks": abl["edges_satisfy_both"] > 0,
    }
    return {"schema": "cbmd.petri-marked-graph.v1", "nets": trials,
            "agree": agree, "disagree": disagree,
            "preserving": pres, "not_preserving": nonpres,
            "with_multi_input_transition": multi,
            "with_multi_input_not_preserving": multi_np,
            "ablation_wrong_verdicts": abl, "free_choice_nets_rejected": rejected, "samples": samples, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["the polynomial procedure is a written argument corroborated by census; it is not compiled",
                          "marked graphs are a classical tractable class; no novelty is claimed for the technique"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 20000)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
