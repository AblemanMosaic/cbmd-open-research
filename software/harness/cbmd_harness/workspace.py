from __future__ import annotations

from pathlib import Path
from typing import Any

from .canonical import load_json, write_json
from .contracts import load_and_verify_specs
from .refusals import Refusal


def initialize_workspace(template: Path, destination: Path, execution_roots: list[Path]) -> dict[str, Any]:
    """Create a fresh local successor, never inherit the producer's authority."""
    destination = destination.resolve()
    if destination.exists() and (not destination.is_dir() or any(destination.iterdir())):
        raise Refusal("CBMD_WORKSPACE_NOT_EMPTY", str(destination))
    if not execution_roots:
        raise Refusal("CBMD_EXECUTION_ROOT_REQUIRED", "name at least one explicit local project directory")
    roots = []
    for candidate in execution_roots:
        resolved = candidate.resolve(strict=True)
        if not resolved.is_dir() or resolved == Path(resolved.anchor) or resolved == Path.home().resolve():
            raise Refusal("CBMD_EXECUTION_ROOT_TOO_BROAD", str(resolved))
        roots.append(str(resolved))
    load_and_verify_specs(template)
    spec = destination / "spec"
    spec.mkdir(parents=True)
    for source in sorted((template / "spec").glob("*")):
        if source.is_file():
            (spec / source.name).write_bytes(source.read_bytes())
    authority = load_json(spec / "CBMD-AUTHORITY.json")
    authority["standing"] = "LOCAL_OPERATOR_CONFIGURED"
    authority["allowed_execution_roots"] = sorted(set(roots))
    authority["source"] = {
        "kind": "EXPLICIT_LOCAL_CONFIGURATION",
        "summary": "The local operator selected these project roots. No project, publication, remote-write, or external authority is inherited.",
    }
    write_json(spec / "CBMD-AUTHORITY.json", authority)
    return {"schema": "cbmd.workspace-initialization.v1", "status": "PASS",
            "workspace": str(destination), "execution_roots": authority["allowed_execution_roots"],
            **load_and_verify_specs(destination), "authority_effect": "NONE"}
