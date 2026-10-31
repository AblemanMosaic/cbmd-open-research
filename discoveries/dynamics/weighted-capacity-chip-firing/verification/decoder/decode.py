"""Kernel-certified verdicts for weighted instances given as files.

Input (JSON): {"vertices": [names], "sink": name,
               "arcs": [[from, to, multiplicity], ...],   # arcs into the sink allowed
               "capacity": {name: int}}                    # nonsink vertices

The decoder validates (failing closed: unknown name, loop, repeated arc,
non-positive multiplicity, arc out of the sink, missing capacity, a vertex with
no out-arc), then emits a Lean module in which

  * `mult` comes from an explicit list, and `outdegree` is computed IN LEAN as
    the sum of the nonsink multiplicities plus the sink multiplicity, so it is
    faithful by construction;
  * the verdict is a theorem: `TerminalStable mult outdegree capacity` or its
    negation, obtained from `terminalStable_iff_decide` and a `decide` proof of
    `decideTerminalStable .. = true` (or `= false`) -- checked by the kernel;
  * Lean evaluates the emitted lists and outdegrees, and the decoder accepts
    only if they reconstruct the input exactly.

Arbitrary digraphs are allowed: the characterization of revision 0.9.0 does not
need an order.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN = HERE.parent / "lean"


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


class Refusal(ValueError):
    def __init__(self, code):
        super().__init__(code)
        self.code = code


def validate(g):
    names, sink = g.get("vertices"), g.get("sink")
    if not isinstance(names, list) or len(set(names)) != len(names) or sink not in names:
        raise Refusal("BAD_VERTICES")
    seen = {}
    for a in g.get("arcs", []):
        if not (isinstance(a, list) and len(a) == 3 and a[0] in names and a[1] in names):
            raise Refusal("UNKNOWN_VERTEX")
        if not (isinstance(a[2], int) and a[2] > 0):
            raise Refusal("NONPOSITIVE_MULTIPLICITY")
        if a[0] == a[1]:
            raise Refusal("LOOP")
        if a[0] == sink:
            raise Refusal("ARC_OUT_OF_SINK")
        if (a[0], a[1]) in seen:
            raise Refusal("REPEATED_ARC")
        seen[(a[0], a[1])] = a[2]
    nonsink = sorted(v for v in names if v != sink)
    cap = g.get("capacity", {})
    if any(not (isinstance(cap.get(v), int) and cap[v] >= 0) for v in nonsink):
        raise Refusal("MISSING_CAPACITY")
    if any(not any(u == v for (u, _w) in seen) for v in nonsink):
        raise Refusal("NO_OUT_ARC")
    return nonsink, seen, cap


def emit(g, ns, claim=None, corrupt=None):
    nonsink, arcs, cap = validate(g)
    idx = {v: i for i, v in enumerate(nonsink)}
    n = len(nonsink)
    M = [[arcs.get((u, w), 0) for w in nonsink] for u in nonsink]
    S = [arcs.get((u, g["sink"]), 0) for u in nonsink]
    C = [cap[v] for v in nonsink]
    if corrupt == "drop_arc":
        for i in range(n):
            for j in range(n):
                if M[i][j]:
                    M[i][j] = 0
                    break
            else:
                continue
            break
    rows = "[" + ", ".join("[" + ", ".join(map(str, r)) + "]" for r in M) + "]"
    body = f"""namespace {ns}
open CBMDWeightedDynamics
def multList : List (List Nat) := {rows}
def sinkList : List Nat := {S}
def capList : List Nat := {C}
def mult (u v : Fin {n}) : Nat := (multList.getD u.val []).getD v.val 0
def outdegree (u : Fin {n}) : Nat :=
  (List.finRange {n}).foldl (fun acc v => acc + mult u v) 0 + sinkList.getD u.val 0
def capacity (v : Fin {n}) : Nat := capList.getD v.val 0
theorem pos : ∀ u, 0 < outdegree u := by decide
"""
    if claim not in ("STABLE", "UNSTABLE"):
        raise ValueError("claim must be STABLE or UNSTABLE")
    if claim == "STABLE":
        body += """theorem cert : decideTerminalStable mult outdegree capacity = true := by decide
theorem verdict : TerminalStable mult outdegree capacity :=
  (terminalStable_iff_decide mult outdegree capacity pos).mpr cert
"""
    else:
        body += """theorem cert : decideTerminalStable mult outdegree capacity = false := by decide
theorem verdict : ¬ TerminalStable mult outdegree capacity := fun h => by
  have := (terminalStable_iff_decide mult outdegree capacity pos).mp h
  rw [cert] at this; exact Bool.noConfusion this
"""
    body += f"""#eval IO.println s!"DECODED|{{multList}}|{{sinkList}}|{{capList}}|{{(List.finRange {n}).map outdegree}}"
#print axioms verdict
end {ns}
"""
    return body, nonsink


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


def run_lean(src):
    env = dict(os.environ)
    if env.get("CBMD_LEAN_BIN"):
        env["PATH"] = env["CBMD_LEAN_BIN"] + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = str(built_library(env))
    d = Path(tempfile.mkdtemp(prefix="cbmd-wdecode-"))
    (d / "Decoded.lean").write_text("import CBMDWeightedDynamics\n" + src, encoding="utf-8")
    p = subprocess.run([tool_path(env, "lean"), str(d / "Decoded.lean")],
                       capture_output=True, text=True, env=env,
                       timeout=3600)
    return p.returncode, p.stdout


def parse(line):
    _, mult, sinks, caps, outd = line.strip().split("|")
    rows = [[int(x) for x in re.findall(r"\d+", r)] for r in re.findall(r"\[([\d, ]*)\]", mult[1:-1])]
    ints = lambda s: [int(x) for x in re.findall(r"\d+", s)]
    return rows, ints(sinks), ints(caps), ints(outd)


def certify(g, nonsink, parsed):
    rows, sinks, caps, outd = parsed
    n = len(nonsink)
    arcs = {(nonsink[i], nonsink[j], rows[i][j]) for i in range(n) for j in range(n) if rows[i][j]}
    arcs |= {(nonsink[i], g["sink"], sinks[i]) for i in range(n) if sinks[i]}
    true_out = {v: sum(a[2] for a in g["arcs"] if a[0] == v) for v in nonsink}
    return (arcs == {tuple(a) for a in g["arcs"]} and
            {nonsink[i]: caps[i] for i in range(n)} == {v: g["capacity"][v] for v in nonsink} and
            {nonsink[i]: outd[i] for i in range(n)} == true_out)


def ns_for(g):
    return "W" + hashlib.sha256(json.dumps(g, sort_keys=True).encode()).hexdigest()[:12]
