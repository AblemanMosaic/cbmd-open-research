"""Replay the finite FD-C1 evidence from a public checkout."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
DISCOVERY = HERE.parent
ROOT = DISCOVERY.parents[2]
EXPECTED_COUNTS = {"graphs": 340, "systems": 5222, "initial_states": 420840}
EXPECTED_HASHES = {
    "primary": "90c9ceb500bbb18ef9d6b6083e8d45378c16a25693c357c2fb3ddee3a83230f2",
    "boundaries": "a0c370fc0adf9192f66bb49f96fdcd1e323ade88f6ad8a30749ec76229edb04e",
    "independent": "9cd7fb89c0e4ccd45d40add37e91e43fb0a7dbdb95cdc60a0eea0c0c431c9d05",
}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def launch(command: list[str], env: dict[str, str]) -> dict[str, object]:
    completed = subprocess.run(
        command,
        cwd=ROOT,
        env=env,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="replace",
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(
            f"command failed ({completed.returncode}): {command!r}\n{completed.stderr}"
        )
    return {"command": command, "exit_code": completed.returncode}


def main() -> int:
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env.pop("PYTHONPATH", None)
    with tempfile.TemporaryDirectory(prefix="cbmd-fd-public-") as raw:
        out = Path(raw)
        primary = out / "primary.json"
        boundaries = out / "boundaries.json"
        independent = out / "independent.json"
        steps = [
            launch([
                sys.executable, "-B", str(HERE / "reference" / "search_minimal.py"),
                "--max-n", "4", "--extra-capacity", "1", "--output", str(primary),
            ], env),
            launch([
                sys.executable, "-B", str(HERE / "reference" / "search_boundaries.py"),
                "--output", str(boundaries),
            ], env),
            launch([
                sys.executable, "-B", str(HERE / "independent" / "independent_check.py"),
                "--output", str(independent),
            ], env),
        ]
        actual_hashes = {
            "primary": digest(primary),
            "boundaries": digest(boundaries),
            "independent": digest(independent),
        }
        if actual_hashes != EXPECTED_HASHES:
            raise RuntimeError(f"deterministic evidence hash drift: {actual_hashes!r}")
        p = json.loads(primary.read_text(encoding="utf-8"))
        b = json.loads(boundaries.read_text(encoding="utf-8"))
        i = json.loads(independent.read_text(encoding="utf-8"))
        if p["enumerated"] != EXPECTED_COUNTS or p["witness_count"] != 0:
            raise RuntimeError("primary finite box drifted")
        if i["positive_box"]["counts"] != EXPECTED_COUNTS or i["status"] != "PASS":
            raise RuntimeError("independent finite box drifted")
        if len(i["cyclic_witness"]["normal_forms"]) != 2:
            raise RuntimeError("cyclic nonconfluence witness drifted")
        if not i["false_normal_form_boundaries"]["two_cycle"]["capacity_terminal"]:
            raise RuntimeError("two-cycle adverse witness drifted")
        if not i["false_normal_form_boundaries"]["parallel_edge_dag"]["capacity_terminal"]:
            raise RuntimeError("parallel-edge adverse witness drifted")
        if b["cyclic_simple_n3_nonconfluent"] is None:
            raise RuntimeError("boundary search lost cyclic nonconfluence")
        report = {
            "schema": "cbmd.finite_dynamics.public_replay.v1",
            "status": "PASS",
            "counts": EXPECTED_COUNTS,
            "hashes": actual_hashes,
            "steps": steps,
            "independent_producer_import": False,
        }
        print(json.dumps(report, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc)}, sort_keys=True), file=sys.stderr)
        raise SystemExit(1)
