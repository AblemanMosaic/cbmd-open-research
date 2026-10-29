"""Audit or compile the isolated Lean 4.35.0 FD-C1 proof envelope."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys


PROJECT = Path(__file__).resolve().parent
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.35.0"
TOOLCHAIN_DIR = "leanprover--lean4---v4.35.0"
EXPECTED_SOURCES = {
    "CBMDFiniteDynamics.lean",
    "CBMDFiniteDynamics/CapacityBlocked.lean",
    "CBMDFiniteDynamics/FullTheorem.lean",
    "CBMDFiniteDynamics/ConcreteModel.lean",
}


def scrub_lean(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.DOTALL)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def audit() -> list[str]:
    toolchain = (PROJECT / "lean-toolchain").read_text(encoding="utf-8").strip()
    if toolchain != EXPECTED_TOOLCHAIN:
        raise ValueError(f"unexpected Lean toolchain: {toolchain}")
    observed = {
        path.relative_to(PROJECT).as_posix() for path in PROJECT.rglob("*.lean")
    }
    if observed != EXPECTED_SOURCES:
        raise ValueError(f"Lean source envelope drift: {sorted(observed)}")
    forbidden = re.compile(r"\b(sorry|admit|axiom)\b")
    for relative in sorted(observed):
        body = scrub_lean((PROJECT / relative).read_text(encoding="utf-8"))
        if forbidden.search(body):
            raise ValueError(f"proof escape in {relative}")
    concrete = (PROJECT / "CBMDFiniteDynamics" / "ConcreteModel.lean").read_text(encoding="utf-8")
    for declaration in (
        "theorem concrete_ordinary_wellFounded",
        "theorem concrete_ordinary_unique_stabilization",
        "theorem fd_c1_concrete",
    ):
        if declaration not in concrete:
            raise ValueError(f"required theorem absent: {declaration}")
    return sorted(observed)


def locate_lake(explicit: str | None) -> str:
    executable = "lake.exe" if os.name == "nt" else "lake"
    candidates = []
    if explicit:
        candidates.append(Path(explicit))
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    candidates.append(elan / "toolchains" / TOOLCHAIN_DIR / "bin" / executable)
    discovered = shutil.which("lake")
    if discovered:
        candidates.append(Path(discovered))
    for candidate in candidates:
        if candidate.is_file():
            return str(candidate.resolve())
    raise ValueError("pinned Lake executable not found; install Lean 4.35.0 with elan")


def build(explicit_lake: str | None) -> dict[str, object]:
    lake = locate_lake(explicit_lake)
    version = subprocess.run(
        [lake, "--version"], cwd=PROJECT, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=False,
    )
    if version.returncode or "Lean version 4.35.0" not in version.stdout:
        raise ValueError(f"unexpected Lake/Lean version: {version.stdout}{version.stderr}")
    compiled = subprocess.run(
        [lake, "build"], cwd=PROJECT, capture_output=True, text=True,
        encoding="utf-8", errors="replace", check=False,
    )
    if compiled.returncode:
        raise RuntimeError(f"lake build failed:\n{compiled.stdout}\n{compiled.stderr}")
    return {"lake_version": version.stdout.strip(), "exit_code": compiled.returncode}


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--audit-only", action="store_true")
    mode.add_argument("--build", action="store_true")
    parser.add_argument("--lake")
    args = parser.parse_args()
    sources = audit()
    result: dict[str, object] = {
        "schema": "cbmd.finite_dynamics.lean_replay.v1",
        "status": "PASS",
        "toolchain": EXPECTED_TOOLCHAIN,
        "sources": sources,
        "compiled": False,
    }
    if args.build:
        result["build"] = build(args.lake)
        result["compiled"] = True
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc)}, sort_keys=True), file=sys.stderr)
        raise SystemExit(1)
