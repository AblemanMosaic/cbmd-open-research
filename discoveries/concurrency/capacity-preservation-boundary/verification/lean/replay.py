"""Source custody, no-escape audit, and optional recompilation for the Petri targets.

    python -B replay.py --audit-only     # hashes + proof-escape scan, no toolchain needed
    python -B replay.py --build          # also runs lake build and #print axioms

`--audit-only` establishes custody and the absence of proof escapes in the source.
It does NOT establish that the sources compile; only `--build` does that, and only
on the host that runs it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TARGETS = [
    "CBMDPetriCapacity.fire_admissible",
    "CBMDPetriCapacity.reach_admissible",
    "CBMDPetriCapacity.preserves_iff_reachable_form",
    "CBMDPetriCapacity.inert_ordDead",
    "CBMDPetriCapacity.increasing_allFull_capDead",
    "CBMDPetriCapacity.increasing_preserves_iff_inert",
    "CBMDPetriCapacity.increasing_firing_breaks_preservation",
    "CBMDPetriCapacity.Flow.obstruction_breaks",
    "CBMDPetriCapacity.Flow.obstructionOfFailure",
    "CBMDPetriCapacity.Flow.preserves_iff_no_obstruction",
    "CBMDPetriCapacity.WFlow.obstruction_breaks",
    "CBMDPetriCapacity.WFlow.obstructionOfFailure",
    "CBMDPetriCapacity.WFlow.preserves_iff_no_obstruction",
    "CBMDPetriCapacity.WFlow.least_closure_is_complete",
    "CBMDPetriCapacity.WFlow.forced_le_of_bad",
    "CBMDPetriCapacity.WFlow.justified_closure_is_complete",
    "CBMDPetriCapacity.SNet.ordEnabled_mono",
    "CBMDPetriCapacity.SNet.capDead_max",
    "CBMDPetriCapacity.SNet.preserves_iff_greatest_ordDead",
    "CBMDPetriCapacity.SNet.capped_ge_of_bad",
    "CBMDPetriCapacity.SNet.preserves_iff_capped_ordDead",
    "CBMDPetriCapacity.SNet.total_lt",
    "CBMDPetriCapacity.SNet.lower_le",
    "CBMDPetriCapacity.SNet.lower_lt",
    "CBMDPetriCapacity.SNet.exists_capped_capDead",
    "CBMDPetriCapacity.SNet.preserves_decided_by_lowering",
    "CBMDPetriCapacity.notCapEnabled_max_of_single",
    "CBMDPetriCapacity.ub_max",
    "CBMDPetriCapacity.lb_max",
    "CBMDPetriCapacity.lower_bound_blocks",
    "CBMDPetriCapacity.upper_bound_blocks",
    "CBMDPetriCapacity.blocked_by_some_literal",
    "CBMDPetriCapacity.Reduction.clause_capEnabled_iff",
    "CBMDPetriCapacity.Reduction.preserves_iff_no_nonzero_model",
    "CBMDPetriCapacity.Reduction.probe_input_places",
    "CBMDPetriCapacity.Reduction.clause_input_places",
    "CBMDPetriCapacity.Reduction.guard_noTautology",
    "CBMDPetriCapacity.Reduction.satisfiable_iff_guard_nonzero",
    "CBMDPetriCapacity.Reduction.preserves_iff_unsatisfiable",
    "CBMDPetriCapacity.Reduction.guard_neg_count",
    "CBMDPetriCapacity.FreeChoice.free_choice",
    "CBMDPetriCapacity.FreeChoice.input_places",
    "CBMDPetriCapacity.FreeChoice.fc_preserves_iff_unsatisfiable",
    "CBMDPetriCapacity.ConflictFree.certificate_of_bad",
    "CBMDPetriCapacity.ConflictFree.end_unique",
    "CBMDPetriCapacity.ConflictFree.bad_of_certificate",
    "CBMDPetriCapacity.ConflictFree.not_preserves_iff_certificate",
    "CBMDPetriCapacity.InputLess.inet_conflictFree",
    "CBMDPetriCapacity.InputLess.satisfiable_of_capDead",
    "CBMDPetriCapacity.InputLess.inputless_preserves_iff_unsatisfiable",
    "CBMDPetriCapacity.ConflictFree.alive_fix",
    "CBMDPetriCapacity.ConflictFree.closed_sub_iter",
    "CBMDPetriCapacity.ConflictFree.certificate_iff_alive",
    "CBMDPetriCapacity.ConflictFree.preserves_iff_decide",
    "CBMDPetriCapacity.ConflictFree.stepP_iff_stepT",
    "CBMDPetriCapacity.ConflictFree.preserves_iff_decideFast",
    "CBMDPetriCapacity.DegreeTwo.at_most_two_consumers",
    "CBMDPetriCapacity.DegreeTwo.free_choice",
    "CBMDPetriCapacity.DegreeTwo.satisfiable_of_bad",
    "CBMDPetriCapacity.DegreeTwo.degreeTwo_preserves_iff_unsatisfiable",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# A proof escape is one of these as a Lean token, not as a word inside a comment.
ESCAPE = re.compile(r"(?<![A-Za-z0-9_.])(sorry|admit|sorryAx)(?![A-Za-z0-9_])")
COMMENT_BLOCK = re.compile(r"/-.*?-/", re.DOTALL)
COMMENT_LINE = re.compile(r"--[^\n]*")
AXIOM_DECL = re.compile(r"^\s*axiom\s", re.MULTILINE)


def strip_comments(text: str) -> str:
    return COMMENT_LINE.sub("", COMMENT_BLOCK.sub("", text))


def sources() -> list[Path]:
    return sorted(p for p in HERE.rglob("*.lean") if ".lake" not in p.parts)


def audit() -> dict:
    members = []
    escapes = []
    for path in sources():
        raw = path.read_bytes()
        code = strip_comments(raw.decode("utf-8"))
        hits = sorted({m.group(1) for m in ESCAPE.finditer(code)})
        if hits or AXIOM_DECL.search(code):
            escapes.append({"path": path.relative_to(HERE).as_posix(),
                            "tokens": hits, "axiom_declaration": bool(AXIOM_DECL.search(code))})
        members.append({"path": path.relative_to(HERE).as_posix(),
                        "bytes": len(raw), "sha256": hashlib.sha256(raw).hexdigest()})
    toolchain = (HERE / "lean-toolchain").read_text(encoding="utf-8").strip()
    return {
        "schema": "cbmd.petri-lean-audit.v1",
        "toolchain": toolchain,
        "dependencies": [],
        "members": members,
        "target_declarations": TARGETS,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "proof_escapes": escapes,
        "no_escape": not escapes,
        "lean_recompiled": False,
        "actual_axiom_dependencies_checked": False,
        "independent_verification": False,
    }


def build(receipt: dict) -> dict:
    env = dict(os.environ)
    if env.get("CBMD_LEAN_BIN"):
        env["PATH"] = env["CBMD_LEAN_BIN"] + os.pathsep + env.get("PATH", "")
    lake = shutil.which("lake", path=env.get("PATH"))
    lean = shutil.which("lean", path=env.get("PATH"))
    if lake is None or lean is None:
        receipt["build_status"] = "LAKE_NOT_AVAILABLE"
        return receipt
    proc = subprocess.run([lake, "build"], cwd=HERE, capture_output=True, text=True, env=env)
    receipt["build_status"] = "PASS" if proc.returncode == 0 else "FAIL"
    receipt["build_stderr_tail"] = proc.stderr[-2000:]
    if proc.returncode != 0:
        return receipt
    receipt["lean_recompiled"] = True
    probe = HERE / ".axiom_probe.lean"
    probe.write_text("import CBMDPetriCapacity\n"
                     + "".join(f"#print axioms {t}\n" for t in TARGETS), encoding="utf-8")
    try:
        env_path = HERE / ".lake" / "build" / "lib" / "lean"
        out = subprocess.run([lean, str(probe)], cwd=HERE, capture_output=True, text=True,
                             env={**env, "LEAN_PATH": str(env_path)})
        text = out.stdout
        receipt["axiom_report"] = text.strip()
        found: set[str] = set()
        for token in re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", text.replace("\n", " ").split("depends on axioms:", 1)[-1] if "depends on axioms:" in text else ""):
            pass
        for chunk in text.split("depends on axioms:")[1:]:
            segment = chunk.split("'")[0]
            for name in re.findall(r"[A-Za-z_][A-Za-z0-9_.]*", segment):
                found.add(name)
        receipt["actual_axiom_dependencies_checked"] = True
        receipt["axioms_observed"] = sorted(found)
        receipt["axioms_within_allowlist"] = found.issubset(ALLOWED_AXIOMS)
        if "does not depend on any axioms" in text:
            receipt["some_target_axiom_free"] = True
    finally:
        probe.unlink(missing_ok=True)
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--audit-only", action="store_true")
    parser.add_argument("--build", action="store_true")
    parser.add_argument("--write", type=str, default=None)
    args = parser.parse_args()
    receipt = audit()
    if args.build:
        receipt = build(receipt)
    ok = receipt["no_escape"]
    if args.build:
        ok = ok and receipt.get("build_status") == "PASS" and receipt.get("axioms_within_allowlist", False)
    receipt["status"] = "PASS" if ok else "FAIL"
    receipt["authority_effect"] = "NONE"
    text = json.dumps(receipt, indent=1, sort_keys=True)
    if args.write:
        Path(args.write).write_text(text + "\n", encoding="utf-8")
    print(text)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
