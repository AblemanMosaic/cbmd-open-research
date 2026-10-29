"""Recompile the pinned CBMD Lean proof envelope and emit an exact receipt."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

from verify_proof_sources import ROOT, verify as verify_sources


PROJECT = ROOT / "proofs" / "native"
DEFAULT_MANIFEST = PROJECT / "SOURCE_MANIFEST.json"
TOOLCHAIN_DIR = "leanprover--lean4---v4.34.1"
EXPECTED_LEAN_VERSION = "4.34.1"
AUDIT_MODULE = "OAI.CBMDReplay"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def locate_lake(explicit: str | None) -> Path:
    candidates: list[Path] = []
    if explicit:
        candidates.append(Path(explicit))
    elan = Path(os.environ.get("ELAN_HOME", Path.home() / ".elan"))
    executable = "lake.exe" if os.name == "nt" else "lake"
    candidates.append(elan / "toolchains" / TOOLCHAIN_DIR / "bin" / executable)
    discovered = shutil.which("lake")
    if discovered:
        candidates.append(Path(discovered))
    for candidate in candidates:
        if candidate.is_file():
            return candidate.resolve()
    raise ValueError("pinned Lake executable not found; install Lean 4.34.1 with elan")


def run(
    command: list[str],
    cwd: Path,
    timeout: int = 3600,
    environment: dict[str, str] | None = None,
) -> dict[str, object]:
    started = time.monotonic()
    completed = subprocess.run(
        command,
        cwd=cwd,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
        timeout=timeout,
        shell=False,
        env=environment,
    )
    stdout = completed.stdout.encode("utf-8")
    stderr = completed.stderr.encode("utf-8")
    return {
        "argv": command,
        "cwd": cwd.relative_to(ROOT).as_posix(),
        "exit_code": completed.returncode,
        "duration_seconds": round(time.monotonic() - started, 3),
        "stdout_sha256": digest(stdout),
        "stderr_sha256": digest(stderr),
        "stdout_tail": completed.stdout[-4000:],
        "stderr_tail": completed.stderr[-4000:],
    }


def require_success(step: dict[str, object], label: str) -> None:
    if step["exit_code"] != 0:
        raise ValueError(f"{label} failed with exit code {step['exit_code']}")


def verify_dependencies(git: str, lock: dict[str, object], steps: list[dict[str, object]]) -> list[dict[str, str]]:
    packages_dir = PROJECT / lock["packagesDir"]
    realized: list[dict[str, str]] = []
    for package in lock["packages"]:
        package_dir = packages_dir / package["name"]
        if not package_dir.is_dir():
            raise ValueError("pinned dependency checkout absent: " + package["name"])
        safe = f"safe.directory={package_dir.resolve().as_posix()}"
        head_step = run([git, "-c", safe, "-C", str(package_dir), "rev-parse", "HEAD"], ROOT)
        steps.append(head_step)
        require_success(head_step, "dependency revision inspection")
        actual = str(head_step["stdout_tail"]).strip().lower()
        if actual != package["rev"]:
            raise ValueError(f"dependency revision mismatch for {package['name']}: {actual}")
        clean_step = run(
            [git, "-c", safe, "-C", str(package_dir), "status", "--porcelain", "--untracked-files=no"],
            ROOT,
        )
        steps.append(clean_step)
        require_success(clean_step, "dependency cleanliness inspection")
        if str(clean_step["stdout_tail"]).strip():
            raise ValueError("tracked dependency files are modified: " + package["name"])
        realized.append({"name": package["name"], "revision": actual})
    return realized


def execute(args: argparse.Namespace) -> tuple[int, dict[str, object]]:
    receipt: dict[str, object] = {
        "schema": "cbmd.lean-replay-receipt.v1",
        "status": "RUNNING",
        "scope": "PINNED_SOURCE_RECOMPILE_AND_LOGICAL_DEPENDENCY_AUDIT",
        "authority_effect": "NONE",
        "independent_verification": False,
        "steps": [],
    }
    try:
        manifest_path = Path(args.manifest).resolve() if args.manifest else DEFAULT_MANIFEST
        custody = verify_sources(manifest_path)
        receipt["source_custody"] = custody
        manifest = json.loads(manifest_path.read_text(encoding="utf-8-sig"))
        if args.fresh and (PROJECT / ".lake" / "build" / "lib" / "lean" / "OAI").exists():
            raise ValueError("--fresh refuses a project containing pre-existing OAI build outputs")

        lake = locate_lake(args.lake)
        version_step = run([str(lake), "--version"], PROJECT, timeout=120)
        receipt["steps"].append(version_step)
        require_success(version_step, "Lake version check")
        version_text = str(version_step["stdout_tail"]) + str(version_step["stderr_tail"])
        if EXPECTED_LEAN_VERSION not in version_text:
            raise ValueError("Lake is not bound to Lean " + EXPECTED_LEAN_VERSION)

        lock_path = PROJECT / "lake-manifest.json"
        lock_before = lock_path.read_bytes()
        if args.prepare:
            prepare_step = run([str(lake), "update"], PROJECT)
            receipt["steps"].append(prepare_step)
            require_success(prepare_step, "pinned dependency preparation")
            if lock_path.read_bytes() != lock_before:
                raise ValueError("lake update changed the committed dependency lock")
        elif not (PROJECT / ".lake" / "packages").is_dir():
            raise ValueError("dependency checkout absent; use --prepare or provide a pinned cache")

        git = shutil.which("git")
        if not git:
            raise ValueError("git is required to verify dependency revisions")
        lock = json.loads(lock_before.decode("utf-8-sig"))
        receipt["dependencies"] = verify_dependencies(git, lock, receipt["steps"])

        lake_environment = os.environ.copy()
        for index, package in enumerate(lock["packages"]):
            package_dir = (PROJECT / lock["packagesDir"] / package["name"]).resolve()
            lake_environment[f"GIT_CONFIG_KEY_{index}"] = "safe.directory"
            lake_environment[f"GIT_CONFIG_VALUE_{index}"] = package_dir.as_posix()
        lake_environment["GIT_CONFIG_COUNT"] = str(len(lock["packages"]))

        targets = list(manifest["targets"]) + [AUDIT_MODULE]
        build_step = run([str(lake), "build", *targets], PROJECT, environment=lake_environment)
        receipt["steps"].append(build_step)
        require_success(build_step, "Lean target build")

        audit_source = PROJECT / "lean" / "OAI" / "CBMDReplay.lean"
        audit_step = run(
            [str(lake), "env", "lean", "-DwarningAsError=true", str(audit_source)],
            PROJECT,
            environment=lake_environment,
        )
        receipt["steps"].append(audit_step)
        require_success(audit_step, "logical dependency audit")

        receipt.update({
            "status": "PASS",
            "lean_recompiled": True,
            "actual_logical_dependencies_checked": True,
            "kernel_check_disabled": False,
            "fresh_project_outputs_required": bool(args.fresh),
            "dependency_preparation_requested": bool(args.prepare),
            "target_modules": targets,
            "allowed_logical_dependencies": manifest["allowed_axioms"],
            "manifest_sha256": digest(manifest_path.read_bytes()),
            "lock_sha256": digest(lock_before),
        })
        return 0, receipt
    except (KeyError, OSError, subprocess.SubprocessError, TypeError, UnicodeError, ValueError) as exc:
        receipt.update({
            "status": "FAIL",
            "error": str(exc),
            "lean_recompiled": False,
            "actual_logical_dependencies_checked": False,
        })
        return 1, receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", help="source manifest path")
    parser.add_argument("--lake", help="exact Lake executable path")
    parser.add_argument("--prepare", action="store_true", help="acquire/update pinned dependencies")
    parser.add_argument("--fresh", action="store_true", help="refuse pre-existing project OAI outputs")
    parser.add_argument("--receipt", help="write the JSON receipt to this path")
    args = parser.parse_args()
    code, receipt = execute(args)
    rendered = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.receipt:
        destination = Path(args.receipt)
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_text(rendered, encoding="utf-8", newline="\n")
    print(rendered, end="")
    return code


if __name__ == "__main__":
    sys.exit(main())
