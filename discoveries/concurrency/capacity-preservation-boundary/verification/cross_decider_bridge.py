"""Two compiled deciders, from two dossiers, on the same instances.

A chip-firing system is a Petri net with one place per vertex and one
transition per vertex, consuming outdegree(v) from its own place and producing
mult(v,w) into each other place.  Each place is consumed only by its vertex's
transition, so the net is conflict-free, and positive outdegree gives every
transition an input place.  Under that translation, "the capacity invents no
deadlock" (this dossier's `Preserves`) and "every admissible capacity-terminal
state is ordinarily stable" (`TerminalStable` in CBMD-DYN-WEIGHTED-CAPACITY-001)
say the same thing.

The two dossiers formalize them independently, in separate Lean projects, and
each has a decider proved correct: `decidePreservesFast` (revision 0.15.0 here)
and `decideTerminalStable` (revision 0.11.0 there).  This script has Lean run
both on the same random systems and compares them with each other and with the
weighted dossier's simulated transfer.

Gates: the two Lean deciders agree on every system; both agree with simulated
transfer; both verdicts occur.  Requires the pinned toolchain.
"""
from __future__ import annotations

import json
import os
import random
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from lean_decider_bridge import built_library as petri_library  # noqa: E402

WEIGHTED = HERE.parents[2] / "dynamics" / "weighted-capacity-chip-firing" / "verification"
sys.path.insert(0, str(WEIGHTED / "reference"))
from characterize import digraphs, od, transfer_holds  # noqa: E402
import importlib.util as _ilu  # noqa: E402
_spec = _ilu.spec_from_file_location("weighted_lean_decider_bridge",
                                     WEIGHTED / "reference" / "lean_decider_bridge.py")
_wmod = _ilu.module_from_spec(_spec)
_spec.loader.exec_module(_wmod)
weighted_library = _wmod.built_library


def run_lean(src, lib, env):
    env = dict(env)
    env["LEAN_PATH"] = str(lib)
    d = Path(tempfile.mkdtemp(prefix="cbmd-cross-"))
    (d / "X.lean").write_text(src, encoding="utf-8")
    p = subprocess.run(["lean", str(d / "X.lean")], capture_output=True, text=True, env=env,
                       timeout=3600)
    out = {}
    for line in p.stdout.splitlines():
        if line.startswith("V"):
            k, v = line.split()
            out[int(k[1:])] = v == "true"
    return p.returncode, out


def mat(rows):
    return "#[" + ", ".join("#[" + ", ".join(map(str, r)) + "]" for r in rows) + "]"


def run(count=300, seed=515):
    env = dict(os.environ)
    if env.get("CBMD_LEAN_BIN"):
        env["PATH"] = env["CBMD_LEAN_BIN"] + os.pathsep + env.get("PATH", "")
    rng = random.Random(seed)
    pool = [(n, a, s) for n in (1, 2, 3) for a, s in digraphs(n, 2, 1)]
    systems = []
    for _ in range(count):
        n, a, s = rng.choice(pool)
        systems.append((n, a, s, tuple(rng.randint(0, od(a, s, v) + 2) for v in range(n))))
    psrc = ["import CBMDPetriCapacity", "open CBMDPetriCapacity CBMDPetriCapacity.ConflictFree"]
    wsrc = ["import CBMDWeightedDynamics", "open CBMDWeightedDynamics"]
    for i, (n, a, s, c) in enumerate(systems):
        d = [od(a, s, v) for v in range(n)]
        pre = [[d[v] if q == v else 0 for q in range(n)] for v in range(n)]
        post = [[a[v][q] for q in range(n)] for v in range(n)]
        caps = ", ".join(map(str, c))
        psrc += [f"def pre{i} : Array (Array Nat) := {mat(pre)}",
                 f"def post{i} : Array (Array Nat) := {mat(post)}",
                 f"def net{i} : Net {n} {n} := ⟨fun t q => (pre{i}[t.val]!)[q.val]!, fun t q => (post{i}[t.val]!)[q.val]!⟩",
                 f"#eval IO.println s!\"V{i} {{decidePreservesFast net{i} (fun q => (#[{caps}] : Array Nat)[q.val]!)}}\""]
        wsrc += [f"def m{i} : Array (Array Nat) := {mat(a)}",
                 f"#eval IO.println s!\"V{i} {{decideTerminalStable (n := {n}) (fun u v => (m{i}[u.val]!)[v.val]!) "
                 f"(fun v => (#[{', '.join(map(str, d))}] : Array Nat)[v.val]!) (fun v => (#[{caps}] : Array Nat)[v.val]!)}}\""]
    pc, pv = run_lean("\n".join(psrc) + "\n", petri_library(env), env)
    wc, wv = run_lean("\n".join(wsrc) + "\n", weighted_library(env), env)
    agree_dec = agree_sim = yes = 0
    for i, (n, a, s, c) in enumerate(systems):
        sim = transfer_holds(a, s, c, n)
        agree_dec += pv.get(i) is not None and pv.get(i) == wv.get(i)
        agree_sim += pv.get(i) == sim and wv.get(i) == sim
        yes += bool(sim)
    gates = {"deciders_agree": pc == 0 and wc == 0 and agree_dec == count,
             "deciders_agree_with_simulation": agree_sim == count,
             "both_verdicts_occur": 0 < yes < count}
    return {"schema": "cbmd.cross-dossier-decider-bridge.v1", "systems": count,
            "deciders_agree": agree_dec, "agree_with_simulation": agree_sim,
            "transfer": yes, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["the translation between the two formal models is checked on instances, not compiled"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    import shutil
    if shutil.which("lean") is None and not (os.environ.get("CBMD_LEAN_BIN")
                                              and Path(os.environ["CBMD_LEAN_BIN"], "lean").exists()):
        print(json.dumps({"status": "TOOLCHAIN_UNAVAILABLE", "authority_effect": "NONE"}))
        raise SystemExit(3)
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 300)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
