"""Gated test of the weighted decoder.

  * Random instances on arbitrary digraphs (2-5 vertices, multiplicities <= 2,
    cycles allowed) are decoded in one Lean run with the verdict the decoder
    predicts from the three conditions; every verdict theorem must be checked
    by the kernel and every round trip must be exact.
  * For instances with at most 3 vertices the kernel verdict is compared with
    SIMULATED transfer (`characterize.transfer_holds`).
  * Both verdicts must occur.
  * KERNEL CONTROL: claiming the wrong verdict must be rejected by Lean.
  * ROUND-TRIP CONTROL: dropping an arc is internally consistent and so
    accepted by Lean, and must be rejected by the reconstruction.
  * Every verdict theorem depends only on the allowed axioms.
"""
from __future__ import annotations

import json
import random
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "reference"))
from decode import certify, emit, ns_for, parse, run_lean  # noqa: E402
from characterize import candidate_characterization, transfer_holds  # noqa: E402


def random_instance(rng, n):
    names = [f"v{i}" for i in range(n)]
    arcs = []
    for u in names:
        for w in names:
            if u != w and rng.random() < 0.35:
                arcs.append([u, w, rng.randint(1, 2)])
        if rng.random() < 0.7 or not any(a[0] == u for a in arcs):
            arcs.append([u, "s", 1])
    out = {v: sum(a[2] for a in arcs if a[0] == v) for v in names}
    return {"vertices": names + ["s"], "sink": "s", "arcs": arcs,
            "capacity": {v: rng.randint(max(0, out[v] - 1), out[v] + 2) for v in names}}


def predicted(g):
    names = [v for v in g["vertices"] if v != g["sink"]]
    names.sort()
    n = len(names)
    a = [[next((x[2] for x in g["arcs"] if x[0] == u and x[1] == w), 0) for w in names] for u in names]
    s = [next((x[2] for x in g["arcs"] if x[0] == u and x[1] == g["sink"]), 0) for u in names]
    c = [g["capacity"][v] for v in names]
    return n, a, s, c, candidate_characterization(a, s, c, n)


def run(count=80, seed=4):
    rng = random.Random(seed)
    insts, seen = [], set()
    while len(insts) < count:
        g = random_instance(rng, rng.randint(2, 5))
        if ns_for(g) not in seen:
            seen.add(ns_for(g))
            insts.append(g)
    srcs, orders, preds = [], [], []
    for g in insts:
        n, a, s, c, pred = predicted(g)
        src, order = emit(g, ns_for(g), claim="STABLE" if pred else "UNSTABLE")
        srcs.append(src)
        orders.append(order)
        preds.append((n, a, s, c, pred))
    code, out = run_lean("\n".join(srcs))
    lines = [l for l in out.splitlines() if l.startswith("DECODED|")]
    axiom_text = " ".join(l for l in out.splitlines() if not l.startswith("DECODED|"))
    used = set(re.findall(r"\b(propext|Classical\.choice|Quot\.sound|sorryAx)\b", axiom_text))
    certified = sim_checked = sim_agree = stable = 0
    if code == 0 and len(lines) == len(insts):
        for g, order, line, (n, a, s, c, pred) in zip(insts, orders, lines, preds):
            certified += certify(g, order, parse(line))
            stable += pred
            if n <= 3:
                sim_checked += 1
                sim_agree += transfer_holds(a, s, c, n) == pred
    # controls
    g = insts[0]
    pred = preds[0][4]
    src, _ = emit(g, "Wrong", claim="UNSTABLE" if pred else "STABLE")
    wrong_code, _ = run_lean(src)
    # pick the verdict Lean will accept for the corrupted net by trying both
    accepted, line = False, None
    for cl in ("STABLE", "UNSTABLE"):
        src, order = emit(g, "Drop" + cl, claim=cl, corrupt="drop_arc")
        c2, o2 = run_lean(src)
        if c2 == 0:
            accepted = True
            line = next(l for l in o2.splitlines() if l.startswith("DECODED|"))
    drop_rejected = accepted and line is not None and not certify(g, order, parse(line))
    gates = {
        "every_verdict_kernel_checked_and_round_trip_exact": code == 0 and certified == len(insts),
        "kernel_verdict_equals_simulated_transfer": sim_checked > 0 and sim_agree == sim_checked,
        "both_verdicts_occur": 0 < stable < len(insts),
        "kernel_rejects_wrong_verdict": wrong_code != 0,
        "round_trip_rejects_dropped_arc": drop_rejected,
        "axioms_within_allowlist": used <= {"propext", "Classical.choice", "Quot.sound"},
    }
    return {"schema": "cbmd.weighted-decoder-check.v1", "instances": len(insts),
            "certified": certified, "terminal_stable": stable,
            "simulated_checked": sim_checked, "simulated_agree": sim_agree,
            "axioms_observed": sorted(used), "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["certifies the declared JSON format only"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    import shutil as _shutil
    import os as _os
    _bin = _os.environ.get("CBMD_LEAN_BIN", "")

    def _available(name):
        executable = name + (".exe" if _os.name == "nt" else "")
        return _shutil.which(name) is not None or bool(
            _bin and _os.path.isfile(_os.path.join(_bin, executable))
        )

    if not (_available("lean") and _available("lake")):
        print(json.dumps({"status": "TOOLCHAIN_UNAVAILABLE",
                          "detail": "set CBMD_LEAN_BIN to the pinned Lean 4.35.0 bin directory or put lean and lake on PATH",
                          "authority_effect": "NONE"}))
        raise SystemExit(3)
    out = run()
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
