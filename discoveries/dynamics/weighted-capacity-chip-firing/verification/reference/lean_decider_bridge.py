"""The compiled decider, run by Lean, against simulated transfer.

Revision 0.11.0 compiles `terminalStable_iff_decide`: terminal stability holds
exactly when the executable Boolean `decideTerminalStable` returns true.  This
script draws random systems from the census generator (`characterize.digraphs`,
arbitrary digraphs with a reachable sink), has LEAN evaluate the decider on
each (`#eval`), and compares with `characterize.transfer_holds`, which
simulates capacity-blocked firing from every admissible state.

Gates: every Lean verdict equals simulated transfer; both verdicts occur;
systems containing a directed cycle occur.  The Lean library is built in a
private copy outside the checkout; the toolchain comes from `$CBMD_LEAN_BIN`
or PATH.
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
from itertools import product
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent / "lean"
sys.path.insert(0, str(HERE))
from characterize import digraphs, od, transfer_holds  # noqa: E402


def tool_path(env, name):
    executable = name + (".exe" if os.name == "nt" else "")
    bin_dir = env.get("CBMD_LEAN_BIN", "")
    candidate = Path(bin_dir, executable) if bin_dir else None
    if candidate is not None and candidate.is_file():
        return str(candidate.resolve())
    discovered = shutil.which(name, path=env.get("PATH"))
    if discovered:
        return discovered
    raise FileNotFoundError(f"pinned {name} executable not found")


def built_library(env):
    files = sorted(p for p in LEAN.rglob("*") if p.is_file() and ".lake" not in p.parts
                   and (p.suffix in (".lean", ".toml", ".json") or p.name == "lean-toolchain"))
    key = hashlib.sha256(b"".join(p.relative_to(LEAN).as_posix().encode() + p.read_bytes()
                                  for p in files)).hexdigest()[:16]
    work = Path(tempfile.gettempdir()) / f"cbmd-weighted-{key}"
    lib = work / ".lake" / "build" / "lib" / "lean"
    if not (lib / "CBMDWeightedDynamics.olean").exists():
        for p in files:
            dst = work / p.relative_to(LEAN)
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)
        subprocess.run([tool_path(env, "lake"), "build"], cwd=work, env=env, check=True,
                       capture_output=True, timeout=3600)
    return lib


def has_cycle(a, n):
    colour = [0] * n

    def dfs(u):
        colour[u] = 1
        for v in range(n):
            if a[u][v] and (colour[v] == 1 or (colour[v] == 0 and dfs(v))):
                return True
        colour[u] = 2
        return False
    return any(colour[u] == 0 and dfs(u) for u in range(n))


def run(count=500, seed=909):
    env = dict(os.environ)
    if env.get("CBMD_LEAN_BIN"):
        env["PATH"] = env["CBMD_LEAN_BIN"] + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = str(built_library(env))
    rng = random.Random(seed)
    pool = []
    for n in (1, 2, 3):
        for a, s in digraphs(n, 2, 1):
            pool.append((n, a, s))
    systems = []
    for _ in range(count):
        n, a, s = rng.choice(pool)
        c = tuple(rng.randint(0, od(a, s, v) + 2) for v in range(n))
        systems.append((n, a, s, c))
    src = ["import CBMDWeightedDynamics", "open CBMDWeightedDynamics"]
    for i, (n, a, s, c) in enumerate(systems):
        mat = "#[" + ", ".join("#[" + ", ".join(map(str, row)) + "]" for row in a) + "]"
        d = [od(a, s, v) for v in range(n)]
        src.append(f"def m{i} : Array (Array Nat) := {mat}")
        src.append(f"def d{i} : Array Nat := #[{', '.join(map(str, d))}]")
        src.append(f"def c{i} : Array Nat := #[{', '.join(map(str, c))}]")
        src.append(f"#eval IO.println s!\"V{i} {{decideTerminalStable (n := {n}) "
                   f"(fun u v => (m{i}[u.val]!)[v.val]!) (fun v => d{i}[v.val]!) (fun v => c{i}[v.val]!)}}\"")
    d = Path(tempfile.mkdtemp(prefix="cbmd-wdecider-"))
    (d / "Bridge.lean").write_text("\n".join(src) + "\n", encoding="utf-8")
    p = subprocess.run([tool_path(env, "lean"), str(d / "Bridge.lean")],
                       capture_output=True, text=True, env=env,
                       timeout=3600)
    verdicts = {}
    for line in p.stdout.splitlines():
        if line.startswith("V"):
            k, v = line.split()
            verdicts[int(k[1:])] = v == "true"
    agree = disagree = yes = no = cyclic = 0
    for i, (n, a, s, c) in enumerate(systems):
        truth = transfer_holds(a, s, c, n)
        yes += truth
        no += not truth
        cyclic += has_cycle(a, n)
        agree += verdicts.get(i) == truth
        disagree += verdicts.get(i) != truth
    gates = {"lean_verdicts_equal_simulated_transfer": p.returncode == 0 and disagree == 0,
             "both_verdicts_occur": yes > 0 and no > 0,
             "cyclic_systems_occur": cyclic > 0}
    return {"schema": "cbmd.weighted-lean-decider-bridge.v1", "systems": count, "agree": agree,
            "disagree": disagree, "transfer": yes, "no_transfer": no, "with_cycle": cyclic,
            "lean_exit": p.returncode, "gates": gates,
            "status": "PASS" if all(gates.values()) else "FAIL",
            "nonclaims": ["the decider decides terminal stability; agreement with simulated transfer is what this bridge measures"],
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
    out = run(int(sys.argv[1]) if len(sys.argv) > 1 else 500)
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
