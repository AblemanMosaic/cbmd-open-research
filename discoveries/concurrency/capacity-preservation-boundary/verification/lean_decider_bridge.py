"""The compiled decision procedure, run by Lean, against brute force.

Revision 0.15.0 compiles `preserves_iff_decide`: for conflict-free nets in which
every transition has an input place, `Preserves N cap ↔ decidePreserves N cap =
true`, where `decidePreserves` is an executable Boolean function.  This script
generates random such nets, has LEAN evaluate both `decidePreserves` and the
threshold-only `decidePreservesFast` on each (`#eval`), and compares the verdicts with an independent brute force over all
admissible markings (`marked_graph.brute`, built on `petri.capacity_enabled`).

Gates: every Lean verdict equals brute force; both verdicts occur; nets with a
multi-input transition occur.  The Lean library is built in a private copy
outside the checkout.  Requires the pinned toolchain (`$CBMD_LEAN_BIN` or PATH).
"""
from __future__ import annotations

import hashlib
import json
import os
import random
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE / "lean"
sys.path.insert(0, str(HERE))
from conflict_free import random_conflict_free  # noqa: E402
from marked_graph import brute  # noqa: E402


def built_library(env):
    files = sorted(p for p in LEAN.rglob("*") if p.is_file() and ".lake" not in p.parts
                   and (p.suffix in (".lean", ".toml", ".json") or p.name == "lean-toolchain"))
    key = hashlib.sha256(b"".join(p.relative_to(LEAN).as_posix().encode() + p.read_bytes()
                                  for p in files)).hexdigest()[:16]
    work = Path(tempfile.gettempdir()) / f"cbmd-petri-{key}"
    lib = work / ".lake" / "build" / "lib" / "lean"
    if not (lib / "CBMDPetriCapacity.olean").exists():
        for p in files:
            dst = work / p.relative_to(LEAN)
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)
        subprocess.run(["lake", "build"], cwd=work, env=env, check=True,
                       capture_output=True, timeout=3600)
    return lib


def lean_matrix(rows):
    return "#[" + ", ".join("#[" + ", ".join(map(str, r)) + "]" for r in rows) + "]"


def run(count=400, seed=88):
    env = dict(os.environ)
    if env.get("CBMD_LEAN_BIN"):
        env["PATH"] = env["CBMD_LEAN_BIN"] + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = str(built_library(env))
    rng = random.Random(seed)
    nets = []
    for _ in range(count):
        P = rng.randint(1, 5)
        T = rng.randint(1, min(P, 4))
        nets.append((P, T, *random_conflict_free(rng, P, T, rng.choice([1, 2, 3]),
                                                 rng.choice([1, 2, 3]), rng.choice([0.2, 0.4]))))
    src = ["import CBMDPetriCapacity", "open CBMDPetriCapacity CBMDPetriCapacity.ConflictFree"]
    for i, (P, T, pre, post, cap) in enumerate(nets):
        src.append(f"def pre{i} : Array (Array Nat) := {lean_matrix(pre)}")
        src.append(f"def post{i} : Array (Array Nat) := {lean_matrix(post)}")
        src.append(f"def cap{i} : Array Nat := #[{', '.join(map(str, cap))}]")
        src.append(f"def net{i} : Net {P} {T} := ⟨fun t q => (pre{i}[t.val]!)[q.val]!, "
                   f"fun t q => (post{i}[t.val]!)[q.val]!⟩")
        src.append(f"#eval IO.println s!\"V{i} {{decidePreserves net{i} (fun q => cap{i}[q.val]!)}} "
                   f"{{decidePreservesFast net{i} (fun q => cap{i}[q.val]!)}}\"")
    d = Path(tempfile.mkdtemp(prefix="cbmd-decider-"))
    (d / "Bridge.lean").write_text("\n".join(src) + "\n", encoding="utf-8")
    p = subprocess.run(["lean", str(d / "Bridge.lean")], capture_output=True, text=True, env=env,
                       timeout=3600)
    verdicts, fast = {}, {}
    for line in p.stdout.splitlines():
        if line.startswith("V"):
            k, v, f = line.split()
            verdicts[int(k[1:])] = v == "true"
            fast[int(k[1:])] = f == "true"
    agree = disagree = pres = nonpres = multi = 0
    for i, (P, T, pre, post, cap) in enumerate(nets):
        truth = brute(pre, post, cap, P, T)
        pres += truth
        nonpres += not truth
        multi += any(sum(1 for q in range(P) if pre[t][q]) >= 2 for t in range(T))
        if verdicts.get(i) == truth and fast.get(i) == truth:
            agree += 1
        else:
            disagree += 1
    gates = {"lean_verdicts_equal_brute_force": p.returncode == 0 and disagree == 0 and agree == count,
             "both_verdicts_occur": pres > 0 and nonpres > 0,
             "multi_input_nets_occur": multi > 0}
    return {"schema": "cbmd.petri-lean-decider-bridge.v1", "nets": count, "agree": agree,
            "disagree": disagree, "preserving": pres, "not_preserving": nonpres,
            "with_multi_input_transition": multi, "lean_exit": p.returncode, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["Lean's #eval runs the compiled decider through the interpreter; the theorem preserves_iff_decide is what makes its output the answer"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 400)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
