"""Owner-fiber claims against the PACKED REFERENCE, multi-block included.

The standalone verifier `owner_fiber.py` models a single covered block and
imports nothing from the archive.  The open obligation asks for the claims to
hold of the packed definitions, preserving the missing-address,
first-occurrence, repeated-incidence, uncovered-target and exact-owner
branches.  This script does the census half of that: it evaluates the claims
directly against the repository's frozen packed reference,
`discoveries/algorithms/reference-amplitude-cost-model/verification/reference-model/src/owner_sum.py`
(list order, first occurrence, equal-type bucket ranks as blocks, a covered
block count), on layouts with SEVERAL blocks.

  U1  for a target pair and owner, at most one incidence contributes a nonzero
      row, and when one does it is the one the candidate route selects;
  U2  for a list of target pairs, the distinct contributors per owner are at
      most the number of distinct (block, orbit-class) pairs among the targets.

Each packed branch must be exercised: a missing pair, a repeated pair (first
occurrence decides), an uncovered target (rank beyond the covered count), an
exact-owner rejection (equal head words, different owners), and a target in a
block other than 0.  Controls that must fail:

  * BLOCK-BLIND: compare rows across blocks -- U1 must then be violated, so
    the block structure is load-bearing;
  * INCOHERENT: give an incidence a head word different from its owner's at an
    active coordinate -- U1 must then be violated.

This is a census against a Python reference, not a compiled correspondence to
the archive's packed Lean definitions; it does not restore
SOURCE_BOUND_COMPILED.
"""
from __future__ import annotations

import json
import os
import random
import sys
from itertools import product

HERE = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(HERE, "..", "..", "..", "algorithms", "reference-amplitude-cost-model",
                   "verification", "reference-model", "src")
sys.path.insert(0, SRC)
from owner_sum import (Indexed, Layout, Meter, Ring, Scan, candidate,  # noqa: E402
                       evaluate, source_row, validate)


def orbit_class(u, Q):
    return tuple(tuple(sorted((u[t], u[Q + t]))) for t in range(Q))


def contributions(L, pack, pair, owner, ring, m, block_blind=False):
    """Per-incidence contributions of the literal scan, as in owner_sum.evaluate."""
    i = pack.first(pair)
    if i is None:
        return None, []
    loc = pack.lookup(i)
    out = []
    for j, (own, _) in enumerate(L.pairs):
        if own != owner:
            continue
        if loc is None:
            v = (ring.norm(int(i == j)),)
        else:
            jl = pack.lookup(j)
            same = jl is not None and (block_blind or jl[0] == loc[0])
            v = source_row(loc[1], jl[1], L.A, L.R, ring, m) if same else (ring.norm(0),)
        if any(v):
            out.append(j)
    return (i, loc), out


def random_layout(rng, Q, copies, A, R, incoherent=False):
    r = 2
    words = list(product(range(r), repeat=Q))
    heads = words + words[: rng.randint(0, len(words))]          # duplicated heads
    types = list(product(range(r), repeat=2 * Q))
    labels, pairs = [], []
    for _b in range(copies):
        for u in rng.sample(types, len(types)):
            owners = [o for o, h in enumerate(heads) if h == u[:Q]]
            labels.append(u)
            pairs.append((rng.choice(owners), rng.randint(0, 2)))   # repeated pairs on purpose
    for _ in range(rng.randint(0, 3)):                                 # leftovers: uncovered ranks
        u = rng.choice(types)
        labels.append(u)
        pairs.append((rng.choice([o for o, h in enumerate(heads) if h == u[:Q]]), rng.randint(0, 5)))
    if incoherent:
        # re-own one incidence to an owner whose head differs at an active coordinate
        k = rng.randrange(len(labels))
        u = labels[k]
        act = [t for t in range(Q) if u[t] != u[Q + t]]
        if act:
            t = act[0]
            want = list(u[:Q])
            want[t] = u[Q + t]
            o = next(o for o, h in enumerate(heads) if list(h) == want)
            pairs[k] = (o, pairs[k][1])
    return Layout(Q, r, tuple(labels), tuple(pairs), tuple(heads), A, R, None)


def run(trials=300, seed=2026):
    rng = random.Random(seed)
    stats = {"queries": 0, "u1_violations": 0, "candidate_disagreements": 0,
             "off_diagonal_contributors": 0, "u2_sums": 0, "u2_violations": 0, "u2_attained": 0,
             "branch_missing_pair": 0, "branch_repeated_pair": 0, "branch_uncovered_target": 0,
             "branch_exact_owner_rejection": 0, "branch_block_ge_1": 0,
             "control_block_blind_u1_violations": 0, "control_incoherent_u1_violations": 0}
    for _ in range(trials):
        Q = rng.choice([1, 2])
        copies = rng.choice([2, 3])
        A, R = rng.randint(1, 3), rng.randint(1, 3)
        L = random_layout(rng, Q, copies, A, R)
        validate(L)
        m = Meter()
        ring = Ring(None, m)
        pack = Scan(L, m)
        idx = Indexed(L, m)
        pairs = sorted(set(L.pairs)) + [(0, 999)]
        for pair in pairs:
            if L.pairs.count(pair) > 1:
                stats["branch_repeated_pair"] += 1
            for owner in range(len(L.heads)):
                stats["queries"] += 1
                info, contrib = contributions(L, pack, pair, owner, ring, m)
                if info is None:
                    stats["branch_missing_pair"] += 1
                    continue
                i, loc = info
                if loc is None:
                    stats["branch_uncovered_target"] += 1
                elif loc[0] >= 1:
                    stats["branch_block_ge_1"] += 1
                if len(contrib) > 1:
                    stats["u1_violations"] += 1
                stats["off_diagonal_contributors"] += sum(1 for j in contrib if j != i)
                # the candidate route of the packed reference must give the same row
                lit = evaluate(L, pack, pair, owner, "literal_scan", m)
                cand = evaluate(L, idx, pair, owner, "prepared_index", m)
                if lit != cand:
                    stats["candidate_disagreements"] += 1
                if loc is not None:
                    y = candidate(loc[1], L.heads[owner], m)
                    if y is not None:
                        j = idx.vertex(loc[0], y)
                        if L.pairs[j][0] != owner:
                            stats["branch_exact_owner_rejection"] += 1
                # block-blind control
                _, blind = contributions(L, pack, pair, owner, ring, m, block_blind=True)
                if len(blind) > 1:
                    stats["control_block_blind_u1_violations"] += 1
        # U2 on random target lists
        for _ in range(6):
            targets = [rng.choice(pairs[:-1]) for _ in range(rng.randint(1, 4))]
            classes = set()
            for p in targets:
                i = pack.first(p)
                loc = pack.lookup(i)
                classes.add(("uncovered", i) if loc is None else (loc[0], orbit_class(loc[1], Q)))
            for owner in range(len(L.heads)):
                js = set()
                for p in targets:
                    js |= set(contributions(L, pack, p, owner, ring, m)[1])
                stats["u2_sums"] += 1
                if len(js) > len(classes):
                    stats["u2_violations"] += 1
                if len(js) == len(classes):
                    stats["u2_attained"] += 1
        # incoherent control (validation deliberately bypassed)
        Li = random_layout(rng, Q, copies, A, R, incoherent=True)
        mi = Meter()
        pi = Scan(Li, mi)
        for pair in set(Li.pairs):
            for owner in range(len(Li.heads)):
                if len(contributions(Li, pi, pair, owner, Ring(None, mi), mi)[1]) > 1:
                    stats["control_incoherent_u1_violations"] += 1
    gates = {
        "U1_no_violation": stats["u1_violations"] == 0,
        "U1_candidate_route_agrees": stats["candidate_disagreements"] == 0,
        "U1_nondegenerate": stats["off_diagonal_contributors"] > 0,
        "U2_no_violation": stats["u2_violations"] == 0 and stats["u2_sums"] > 0,
        "U2_bound_attained": stats["u2_attained"] > 0,
        "branch_missing_pair_exercised": stats["branch_missing_pair"] > 0,
        "branch_repeated_pair_exercised": stats["branch_repeated_pair"] > 0,
        "branch_uncovered_target_exercised": stats["branch_uncovered_target"] > 0,
        "branch_exact_owner_rejection_exercised": stats["branch_exact_owner_rejection"] > 0,
        "branch_block_ge_1_exercised": stats["branch_block_ge_1"] > 0,
        "control_block_blind_fails": stats["control_block_blind_u1_violations"] > 0,
        "control_incoherent_fails": stats["control_incoherent_u1_violations"] > 0,
    }
    return {"schema": "cbmd.owner-fiber-packed-reference.v1", "trials": trials, **stats,
            "gates": gates, "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": [
                "a census against the repository's frozen Python packed reference, not a compiled correspondence to the archive's packed Lean definitions",
                "does not restore SOURCE_BOUND_COMPILED",
            ],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 300)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
