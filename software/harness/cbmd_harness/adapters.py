from __future__ import annotations

import os
import re
import shutil
import sys
from pathlib import Path
from typing import Any

from .canonical import file_sha256, root, write_json
from .refusals import Refusal


_IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$")


def _local_import_closure(project: Path, source: Path) -> list[Path]:
    lean_root = project / "lean"
    seen = {source.resolve(strict=True)}
    pending = [source]
    while pending:
        current = pending.pop()
        for line in current.read_text(encoding="utf-8").splitlines():
            match = _IMPORT.match(line)
            if match is None:
                continue
            candidate = lean_root / Path(*match.group(1).split("."))
            candidate = candidate.with_suffix(".lean")
            if not candidate.is_file():
                continue
            resolved = candidate.resolve(strict=True)
            if resolved not in seen:
                seen.add(resolved)
                pending.append(resolved)
    seen.remove(source.resolve(strict=True))
    return sorted(seen, key=lambda path: str(path).casefold())


def _find_lake(toolchain: str) -> Path:
    if "/" not in toolchain or ":" not in toolchain:
        raise Refusal("CBMD_LEAN_TOOLCHAIN_REFUSED", toolchain)
    directory_name = toolchain.replace("/", "--").replace(":", "---")
    elan_home = Path(os.environ.get("ELAN_HOME", str(Path.home() / ".elan")))
    candidate = elan_home / "toolchains" / directory_name / "bin" / ("lake.exe" if os.name == "nt" else "lake")
    if not candidate.is_file():
        raise Refusal("CBMD_LAKE_NOT_FOUND", str(candidate))
    return candidate.resolve(strict=True)


def _find_git() -> Path:
    configured = os.environ.get("CBMD_GIT_EXE") or shutil.which("git")
    if configured is None:
        raise Refusal("CBMD_GIT_NOT_FOUND", "Set CBMD_GIT_EXE or install Git on PATH.")
    candidate = Path(configured)
    if not candidate.is_file():
        raise Refusal("CBMD_GIT_NOT_FOUND", str(candidate))
    return candidate.resolve(strict=True)


def plan_lean(
    project: Path,
    module: str,
    output: Path | None = None,
    question_id: str = "CBMD.CURRENT",
    claim_ids: list[str] | None = None,
    authority_id: str = "CBMD.LOCAL.OPERATOR",
) -> dict[str, Any]:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*", module):
        raise Refusal("CBMD_LEAN_MODULE_REFUSED", module)
    project = project.resolve(strict=True)
    if not project.is_dir():
        raise Refusal("CBMD_LEAN_PROJECT_REFUSED", str(project))
    toolchain_path = project / "lean-toolchain"
    lakefile = project / "lakefile.lean"
    manifest = project / "lake-manifest.json"
    for required in (toolchain_path, lakefile, manifest):
        if not required.is_file():
            raise Refusal("CBMD_LEAN_PROJECT_INPUT_MISSING", str(required))
    toolchain = toolchain_path.read_text(encoding="utf-8").strip()
    lake = _find_lake(toolchain)
    git = _find_git()
    source = project / "lean" / Path(*module.split("."))
    source = source.with_suffix(".lean")
    if not source.is_file():
        raise Refusal("CBMD_LEAN_MODULE_MISSING", str(source))
    inputs = [
        {"path": str(toolchain_path), "sha256": file_sha256(toolchain_path), "role": "LEAN_TOOLCHAIN_PIN"},
        {"path": str(lakefile), "sha256": file_sha256(lakefile), "role": "LAKEFILE"},
        {"path": str(manifest), "sha256": file_sha256(manifest), "role": "LAKE_MANIFEST"},
        {"path": str(source), "sha256": file_sha256(source), "role": "TARGET_MODULE"},
        {"path": str(git), "sha256": file_sha256(git), "role": "GIT_EXECUTABLE_PIN"},
    ]
    for imported in _local_import_closure(project, source):
        inputs.append({"path": str(imported), "sha256": file_sha256(imported), "role": "LOCAL_IMPORT"})
    for candidate in (
        project / "provenance" / "LEAN_SOURCE_BOUNDARY.json",
        project / "provenance" / "B4_SOURCE_COMMITMENTS.json",
        project / "provenance" / "SOURCE_BOUNDARY_MANIFEST.json",
        project / "provenance" / "TOOLCHAIN.json",
    ):
        if candidate.is_file():
            inputs.append({"path": str(candidate), "sha256": file_sha256(candidate), "role": "PROVENANCE_PIN"})
    # The request root must not absorb an ephemeral host PATH. Lake and Lean live
    # together in the pinned Elan toolchain, so this is the complete admitted PATH.
    path_value = os.pathsep.join([str(lake.parent), str(git.parent)])
    normalized_claim_ids = list(claim_ids or [])
    environment_delta = {"PATH": path_value}
    package_root = project / ".lake" / "packages"
    safe_repositories = []
    if package_root.is_dir():
        safe_repositories = sorted(
            str(path.resolve()) for path in package_root.iterdir()
            if path.is_dir() and (path / ".git").exists()
        )
    if safe_repositories:
        environment_delta["GIT_CONFIG_COUNT"] = str(len(safe_repositories))
        for index, repository in enumerate(safe_repositories):
            environment_delta[f"GIT_CONFIG_KEY_{index}"] = "safe.directory"
            environment_delta[f"GIT_CONFIG_VALUE_{index}"] = repository
    seed = {
        "project": str(project), "module": module, "toolchain": toolchain,
        "inputs": inputs, "question_id": question_id, "claim_ids": normalized_claim_ids,
        "environment_delta": environment_delta,
    }
    operation_id = "LEAN-" + root(seed)[:24].upper()
    request = {
        "schema": "cbmd.run-request.v1",
        "operation_id": operation_id,
        "question_id": question_id,
        "claim_ids": normalized_claim_ids,
        "runner_id": "CBMD.RUNNER.LEAN_LAKE.V1",
        "argv": [str(lake), "build", module],
        "cwd": str(project),
        "environment_delta": environment_delta,
        "timeout_seconds": 1800,
        "expected_exit_codes": [0],
        "inputs": inputs,
        "outputs": [],
        "claim_boundary": "COMPILED_STATEMENT_ONLY_UNTIL_NO_ESCAPE_AND_CORRESPONDENCE_COURTS_PASS",
        "known_remainder": [
            "Module import and build success do not establish absence of sorry or added axioms.",
            "Compiled algebra does not establish source transport without correspondence evidence."
        ],
        "authority_id": authority_id
    }
    if output is not None:
        write_json(output, request)
    return request


def plan_python(
    script: Path, cwd: Path, output: Path | None = None,
    question_id: str = "CBMD.LOCAL.PROBE", claim_ids: list[str] | None = None,
    authority_id: str = "CBMD.LOCAL.OPERATOR",
) -> dict[str, Any]:
    script = script.resolve(strict=True)
    cwd = cwd.resolve(strict=True)
    if not script.is_file() or not cwd.is_dir():
        raise Refusal("CBMD_PYTHON_INPUT_REFUSED", "script file and working directory required")
    inputs = [{"path": str(script), "sha256": file_sha256(script), "role": "SCRIPT"}]
    seed = {"inputs": inputs, "cwd": str(cwd), "question_id": question_id,
            "claim_ids": list(claim_ids or []), "executable": file_sha256(Path(sys.executable))}
    request = {
        "schema": "cbmd.run-request.v1", "operation_id": "PYTHON-" + root(seed)[:24].upper(),
        "question_id": question_id, "claim_ids": list(claim_ids or []),
        "runner_id": "CBMD.RUNNER.PYTHON.V1", "argv": [sys.executable, str(script)],
        "cwd": str(cwd), "environment_delta": {}, "timeout_seconds": 60,
        "expected_exit_codes": [0], "inputs": inputs, "outputs": [],
        "claim_boundary": "PROCESS_OBSERVATION_ONLY; FINITE_COVERAGE_REQUIRES_SEPARATE_ASSESSMENT",
        "known_remainder": ["A passing script does not establish a general mathematical theorem.",
                            "Imported files and undeclared resources are outside this single-script plan."],
        "authority_id": authority_id,
    }
    if output is not None:
        write_json(output, request)
    return request
