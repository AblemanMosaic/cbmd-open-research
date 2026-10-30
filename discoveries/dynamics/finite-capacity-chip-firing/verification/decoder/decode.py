"""Checked decoding of an external graph instance into the Lean parameters.

The compiled theorem `fd_c1_concrete` takes an edge relation and an outdegree
function as parameters; it cannot know whether a caller supplied the true ones
for some graph file.  This decoder closes that gap for a declared file format:

    {"vertices": [names], "sink": name,
     "edges": [[from, to], ...],          # unit edges; edges into the sink allowed
     "capacity": {name: int, ...}}         # nonsink vertices

1. VALIDATE, failing closed with a named refusal: unknown names, loops, a
   repeated edge (the theorem is about unit edges), an edge out of the sink, a
   missing or negative capacity, a directed cycle among nonsink vertices, a
   vertex with no out-edge, and C(v) < d(v).
2. RELABEL the nonsink vertices in a deterministic topological order (Kahn,
   ties broken by name), so edges point forward.
3. EMIT a Lean module defining `edge` from an explicit edge list, `outdegree`
   as the number of nonsink out-edges PLUS the number of sink edges (so it is
   faithful to `edge` by construction), and `capacity`; prove the three
   hypotheses of `fd_c1_concrete` by `decide` -- i.e. by the kernel, not by
   the decoder -- and state the instance theorem.
4. ROUND-TRIP: Lean itself evaluates the emitted edge list, sink edges and
   capacities (`#eval`), and the decoder reconstructs the original graph from
   that output and the recorded name table.  The decoding is accepted only if
   the reconstruction equals the input.

The decoder's own checks are a convenience; the kernel's `decide` and the
round-trip are the certificate.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_PROJECT = HERE.parent / "lean"


class Refusal(ValueError):
    def __init__(self, code):
        super().__init__(code)
        self.code = code


def validate(g):
    names = g.get("vertices")
    sink = g.get("sink")
    if not isinstance(names, list) or len(set(names)) != len(names) or sink not in names:
        raise Refusal("BAD_VERTICES")
    edges = g.get("edges", [])
    seen = set()
    for e in edges:
        if not (isinstance(e, list) and len(e) == 2 and e[0] in names and e[1] in names):
            raise Refusal("UNKNOWN_VERTEX")
        if e[0] == e[1]:
            raise Refusal("LOOP")
        if e[0] == sink:
            raise Refusal("EDGE_OUT_OF_SINK")
        if tuple(e) in seen:
            raise Refusal("REPEATED_EDGE")
        seen.add(tuple(e))
    nonsink = [v for v in names if v != sink]
    cap = g.get("capacity", {})
    for v in nonsink:
        if not (isinstance(cap.get(v), int) and cap[v] >= 0):
            raise Refusal("MISSING_CAPACITY")
    out = {v: [w for (u, w) in seen if u == v and w != sink] for v in nonsink}
    sinkdeg = {v: sum(1 for (u, w) in seen if u == v and w == sink) for v in nonsink}
    deg = {v: len(out[v]) + sinkdeg[v] for v in nonsink}
    if any(deg[v] == 0 for v in nonsink):
        raise Refusal("NO_OUT_EDGE")
    indeg = {v: 0 for v in nonsink}
    for v in nonsink:
        for w in out[v]:
            indeg[w] += 1
    order, ready = [], sorted(v for v in nonsink if indeg[v] == 0)
    while ready:
        v = ready.pop(0)
        order.append(v)
        for w in sorted(out[v]):
            indeg[w] -= 1
            if indeg[w] == 0:
                ready.append(w)
                ready.sort()
    if len(order) != len(nonsink):
        raise Refusal("CYCLE")
    if any(cap[v] < deg[v] for v in nonsink):
        raise Refusal("CAPACITY_BELOW_OUTDEGREE")
    return order, out, sinkdeg, cap


def emit(g, ns, corrupt=None):
    order, out, sinkdeg, cap = validate(g)
    idx = {v: i for i, v in enumerate(order)}
    edges = sorted((idx[u], idx[w]) for u in order for w in out[u])
    sinks = [sinkdeg[v] for v in order]
    caps = [cap[v] for v in order]
    if corrupt == "capacity":
        caps[0] = 0                         # below outdegree, which is positive
    if corrupt == "drop_edge" and edges:
        edges = edges[1:]                   # Lean will accept this; the round trip must not
    if corrupt == "backward_edge" and edges:
        u, w = edges[0]
        edges[0] = (w, u)
    n = len(order)
    lean = f"""namespace {ns}
open CBMDFiniteDynamics
def n : Nat := {n}
def edgeList : List (Nat × Nat) := [{', '.join(f'({u}, {w})' for u, w in edges)}]
def edge (u v : Fin n) : Prop := (u.val, v.val) ∈ edgeList
instance : DecidableRel edge := fun u v => inferInstanceAs (Decidable ((u.val, v.val) ∈ edgeList))
def sinkList : List Nat := {sinks}
def capList : List Nat := {caps}
def sinkEdges (u : Fin n) : Nat := sinkList.getD u.val 0
def outdegree (u : Fin n) : Nat := (List.finRange n).countP (fun v => decide (edge u v)) + sinkEdges u
def capacity (u : Fin n) : Nat := capList.getD u.val 0
theorem ordered : TopologicallyOrdered edge := by
  intro u v h; revert u v; decide
theorem pos : ∀ u, 0 < outdegree u := by decide
theorem capok : ∀ v, outdegree v ≤ capacity v := by decide
theorem transfer (initial : Chips n) :
    ∃ ordinaryNormal,
      Reaches (OrdinaryStep (concreteFire edge outdegree) outdegree) initial ordinaryNormal ∧
      OrdinaryStable outdegree ordinaryNormal ∧
      (∃ final,
        Reaches (CapacityStep edge (concreteFire edge outdegree) outdegree capacity) initial final ∧
        CapacityTerminal edge outdegree capacity final ∧ final = ordinaryNormal) ∧
      (∀ final,
        Reaches (CapacityStep edge (concreteFire edge outdegree) outdegree capacity) initial final →
        CapacityTerminal edge outdegree capacity final → final = ordinaryNormal) :=
  fd_c1_concrete edge outdegree capacity initial ordered pos capok
#eval IO.println s!"DECODED|{{n}}|{{edgeList}}|{{sinkList}}|{{capList}}|{{(List.finRange n).map outdegree}}"
end {ns}
"""
    return lean, order


def reconstruct(evald, order, sink):
    n, edges, sinks, caps, outdeg = evald
    names = list(order)
    E = {(names[u], names[w]) for u, w in edges}
    E |= {(names[i], sink) for i in range(n) for _ in range(sinks[i])}
    return {"vertices": sorted(names + [sink]), "sink": sink,
            "edges": sorted(map(list, E)),
            "capacity": {names[i]: caps[i] for i in range(n)},
            "outdegree_from_lean": {names[i]: outdeg[i] for i in range(n)}}


def built_library(env):
    """Build the dossier's Lean sources in a private copy outside the checkout
    (keyed by their hash), so no build artefact lands in the public tree."""
    import shutil
    import tempfile
    files = sorted(p for p in LEAN_PROJECT.rglob("*") if p.is_file() and ".lake" not in p.parts
                   and p.suffix in (".lean", ".toml", ".json") or p.name == "lean-toolchain")
    key = hashlib.sha256(b"".join(p.relative_to(LEAN_PROJECT).as_posix().encode() + p.read_bytes()
                                  for p in files)).hexdigest()[:16]
    work = Path(tempfile.gettempdir()) / f"cbmd-finite-dynamics-{key}"
    lib = work / ".lake" / "build" / "lib" / "lean"
    if not (lib / "CBMDFiniteDynamics.olean").exists():
        for p in files:
            dst = work / p.relative_to(LEAN_PROJECT)
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)
        subprocess.run(["lake", "build"], cwd=work, env=env, check=True,
                       capture_output=True, timeout=1800)
    return lib


def lean_env():
    """The pinned toolchain: `$CBMD_LEAN_BIN` if set, else `lean` on PATH."""
    env = dict(os.environ)
    if env.get("CBMD_LEAN_BIN"):
        env["PATH"] = env["CBMD_LEAN_BIN"] + os.pathsep + env.get("PATH", "")
    env["LEAN_PATH"] = str(built_library(env))
    return env


def run_lean(src: str):
    import tempfile
    path = Path(tempfile.mkdtemp(prefix="cbmd-decode-")) / "Decoded.lean"
    path.write_text("import CBMDFiniteDynamics\n" + src, encoding="utf-8")
    p = subprocess.run(["lean", str(path)], capture_output=True, text=True, env=lean_env(),
                       timeout=900)
    path.unlink()
    return p.returncode, p.stdout, p.stderr


def parse_eval(line):
    """Parse Lean's own one-line evaluation of the emitted definitions."""
    tag, n, edges, sinks, caps, outdeg = line.strip().split("|")
    assert tag == "DECODED"
    ints = lambda s: [int(x) for x in re.findall(r"\d+", s)]
    pairs = [tuple(map(int, x)) for x in re.findall(r"\((\d+), (\d+)\)", edges)]
    return int(n), pairs, ints(sinks), ints(caps), ints(outdeg)


def normal(g):
    return {"vertices": sorted(g["vertices"]), "sink": g["sink"],
            "edges": sorted(map(list, map(tuple, g["edges"]))),
            "capacity": {v: g["capacity"][v] for v in g["vertices"] if v != g["sink"]}}


def source_outdegree(g):
    return {v: sum(1 for e in g["edges"] if e[0] == v) for v in g["vertices"] if v != g["sink"]}


def certify(g, rec):
    """Accept only if Lean's own evaluation reconstructs the input exactly,
    and Lean's outdegree equals the true outdegree of the input graph."""
    same = {k: rec[k] for k in ("vertices", "sink", "edges", "capacity")} == normal(g)
    return same and rec["outdegree_from_lean"] == source_outdegree(g)


def ns_for(g):
    return "I" + hashlib.sha256(json.dumps(normal(g), sort_keys=True).encode()).hexdigest()[:12]


if __name__ == "__main__":
    g = json.loads(Path(sys.argv[1]).read_text())
    try:
        src, order = emit(g, ns_for(g))
    except Refusal as r:
        print(json.dumps({"status": "REFUSED", "code": r.code}))
        raise SystemExit(2)
    code, out, err = run_lean(src)
    if code:
        print(json.dumps({"status": "LEAN_REJECTED", "stderr": (out + err)[-2000:]}))
        raise SystemExit(1)
    line = next(l for l in out.splitlines() if l.startswith("DECODED|"))
    rec = reconstruct(parse_eval(line), order, g["sink"])
    ok = certify(g, rec)
    print(json.dumps({"status": "CERTIFIED" if ok else "ROUND_TRIP_MISMATCH",
                      "namespace": ns_for(g), "order": order}))
    raise SystemExit(0 if ok else 1)
