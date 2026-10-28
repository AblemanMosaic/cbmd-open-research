"""Replay the bounded reference-amplitude cost evidence from a clean checkout."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent
PINNED = {
    "cost_theorem.py": "6e4b0a774704c4f55ecdf42ec250ed2cf5017ea52b8a9933ecfea599737308e4",
    "cost_theorem.json": "f642175e3d06b07bae7e7ef411027a06fe02296449cf9280212c0aba659c08f2",
    "efficiency.py": "b425158f8a6381fd298d1097dd259f8172172e0ffd4055a6a925eb50bb3861ea",
    "efficiency.json": "917f8bc3f4a24c5757bdb9892aa11bbd8053d953e55a69e16f564f81643d0fb1",
    "src/common.py": "b5a1bb91f736deac7ebbacc057c6a48ec60bb64da63980096b492589ad9c257b",
    "src/owner_sum.py": "72ba4a22b99eb31d14ef961f88681c44998876a0a97a89fc4cf41615d50f4882",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(script: str) -> dict[str, object]:
    completed = subprocess.run(
        [sys.executable, "-I", "-B", str(ROOT / script), str(ROOT / "src")],
        cwd=ROOT,
        capture_output=True,
        text=True,
        encoding="utf-8",
        errors="strict",
        timeout=180,
        check=False,
    )
    if completed.returncode:
        raise RuntimeError(f"{script} failed: {completed.stderr[-2000:]}")
    return json.loads(completed.stdout)


def main() -> int:
    mismatches = [name for name, expected in PINNED.items() if sha256(ROOT / name) != expected]
    if mismatches:
        raise ValueError(f"pinned member hash mismatch: {mismatches}")

    cost = run("cost_theorem.py")
    expected_cost = json.loads((ROOT / "cost_theorem.json").read_text(encoding="utf-8"))
    cost.pop("timing_diagnostic", None)
    expected_cost.pop("timing_diagnostic", None)
    if cost != expected_cost:
        raise ValueError("cost theorem evidence changed")

    efficiency = run("efficiency.py")
    expected_efficiency = json.loads((ROOT / "efficiency.json").read_text(encoding="utf-8"))
    if efficiency != expected_efficiency:
        raise ValueError("efficiency evidence changed")
    if efficiency["T2_unit_hypotheses"]["status"] != "PASS":
        raise ValueError("unit-hypothesis adverse controls failed")

    result = {
        "status": "PASS",
        "scope": "REFERENCE_MODEL_ONLY",
        "cost_exactness_calls": cost["exactness"]["closed_eq_enum"],
        "row_exactness_checks": efficiency["T2_exactness"]["rows_equal"],
        "unit_adverse_controls": len(efficiency["T2_unit_hypotheses"]["adverse_controls"]),
        "native_transport": "NOT_EVALUATED",
        "authority_effect": "NONE",
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc)}, sort_keys=True), file=sys.stderr)
        raise SystemExit(1)
