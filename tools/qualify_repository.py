"""Run repository and per-discovery checks without a shell."""
from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "DISCOVERIES.json"
QUALIFIED_STAGES = {"REVIEW_READY", "RELEASED"}


def run(command: list[str]) -> dict[str, object]:
    expanded = [sys.executable if part == "{python}" else part for part in command]
    completed = subprocess.run(
        expanded,
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    return {
        "command": expanded,
        "exit_code": completed.returncode,
        "stdout": completed.stdout.strip(),
        "stderr": completed.stderr.strip(),
        "status": "PASS" if completed.returncode == 0 else "FAIL",
    }


def main() -> int:
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    gates = [
        ("repository-validator", [sys.executable, "-B", "tools/validate_repository.py"]),
        ("readme-index", [sys.executable, "-B", "tools/render_discovery_index.py", "--check"]),
        ("portable-harness", [sys.executable, "-B", "tools/verify_harness.py"]),
        ("standalone-reference", [sys.executable, "-B", "tools/verify_standalone.py"]),
        ("standalone-unit-tests", [
            sys.executable, "-B", "-m", "unittest", "discover",
            "-s", "software/reference", "-p", "test_*.py",
        ]),
        ("proof-source-custody", [sys.executable, "-B", "tools/verify_proof_sources.py"]),
        ("proof-packaging-adverse-controls", [
            sys.executable, "-B", "tools/test_proof_packaging.py",
        ]),
    ]
    report: dict[str, object] = {
        "schema": "cbmd.open-research.qualification.v2",
        "repository_gates": [],
        "discoveries": [],
    }
    failed = False
    for gate_id, command in gates:
        result = run(command)
        result["id"] = gate_id
        report["repository_gates"].append(result)
        failed = failed or result["status"] != "PASS"

    for row in registry["discoveries"]:
        claim_path = ROOT / row["path"] / "CLAIM.json"
        claim = json.loads(claim_path.read_text(encoding="utf-8"))
        checks = claim.get("checks", [])
        discovery = {
            "id": row["id"],
            "pipeline_stage": row["pipeline_stage"],
            "checks": [],
            "qualification_required": row["pipeline_stage"] in QUALIFIED_STAGES,
        }
        if discovery["qualification_required"] and not checks:
            discovery["status"] = "FAIL"
            discovery["diagnostic"] = "review-ready or released discovery has no declared checks"
            failed = True
        else:
            discovery["status"] = "PASS" if checks else "NOT_QUALIFIED_AT_CURRENT_STAGE"
            for check in checks:
                result = run(check["command"])
                result["id"] = check["id"]
                result["required"] = check.get("required", True)
                discovery["checks"].append(result)
                if result["required"] and result["status"] != "PASS":
                    discovery["status"] = "FAIL"
                    failed = True
        report["discoveries"].append(discovery)

    report["status"] = "FAIL" if failed else "PASS"
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
