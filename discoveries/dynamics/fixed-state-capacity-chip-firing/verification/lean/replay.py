"""Source custody, no-escape audit, and optional recompilation for the fixed-state targets.

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
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
TARGETS = [
    "CBMDFixedState.Star.reach_of_run",
    "CBMDFixedState.Star.run_of_reach",
    "CBMDFixedState.Star.reach_iff",
    "CBMDFixedState.Star.all_fired_reachable_iff",
    "CBMDFixedState.Star.bad_terminal_reachable_iff",
    "CBMDFixedState.Star.run_iff_blocks",
    "CBMDFixedState.Star.normal_form_reachable_iff_partition",
    "CBMDFixedState.Star.fill_eq_mod",
    "CBMDFixedState.Star.stuck_imp_witness",
    "CBMDFixedState.Star.safe_of_no_witness",
    "CBMDFixedState.Star.realise_small",
    "CBMDFixedState.Star.realise_pair",
    "CBMDFixedState.Star.bad_of_small_or_pair_witness",
    "CBMDFixedState.Star.spec_iff",
    "CBMDFixedState.Star.dpWitness_iff",
    "CBMDFixedState.Star.dpFast_eq",
    "CBMDFixedState.Star.safe_of_dpFast",
    "CBMDFixedState.Star.safe_2_3_3",
    "CBMDFixedState.Star.stuck_of_oversize",
    "CBMDFixedState.Star.bad_of_dpBad",
    "CBMDFixedState.Star.classify_safe",
    "CBMDFixedState.Star.classify_bad",
    "CBMDFixedState.Star.bad_2_2_3_3_3",
    "CBMDFixedState.Star.realise_split",
    "CBMDFixedState.Star.bad_of_split",
    "CBMDFixedState.Star.bad_of_triple",
    "CBMDFixedState.Star.bad_of_onebin",
    "CBMDFixedState.Star.bad_of_dpBadT",
    "CBMDFixedState.Star.classifyT_safe",
    "CBMDFixedState.Star.classifyT_bad",
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
        "schema": "cbmd.fixed-state-lean-audit.v1",
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
    if shutil.which("lake") is None:
        receipt["build_status"] = "LAKE_NOT_AVAILABLE"
        return receipt
    proc = subprocess.run(["lake", "build"], cwd=HERE, capture_output=True, text=True)
    receipt["build_status"] = "PASS" if proc.returncode == 0 else "FAIL"
    receipt["build_stderr_tail"] = proc.stderr[-2000:]
    if proc.returncode != 0:
        return receipt
    receipt["lean_recompiled"] = True
    probe = HERE / ".axiom_probe.lean"
    probe.write_text("import CBMDFixedState\n"
                     + "".join(f"#print axioms {t}\n" for t in TARGETS), encoding="utf-8")
    try:
        env_path = HERE / ".lake" / "build" / "lib" / "lean"
        out = subprocess.run(["lean", str(probe)], cwd=HERE, capture_output=True, text=True,
                             env={**__import__("os").environ, "LEAN_PATH": str(env_path)})
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
