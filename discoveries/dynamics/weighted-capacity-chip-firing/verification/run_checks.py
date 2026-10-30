"""Bundled checks for the weighted capacity-blocked chip-firing dossier.

Runs, from a clean checkout and with the standard library only:
  1. the finite bound search (positive control, candidate bound, sharpness),
  2. the independently implemented check of the transfer theorem's conclusion,
  3. the Lean source-custody and no-escape audit.

Lean recompilation is NOT performed here; use
  python -B verification/lean/replay.py --build
on a host with the pinned toolchain.
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PY = sys.executable


def run(name: str, command: list[str]) -> dict:
    proc = subprocess.run(command, cwd=HERE, capture_output=True, text=True)
    row = {"id": name, "command": command, "exit_code": proc.returncode,
           "status": "PASS" if proc.returncode == 0 else "FAIL"}
    try:
        row["result"] = json.loads(proc.stdout)
    except json.JSONDecodeError:
        row["stdout_tail"] = proc.stdout[-1500:]
        row["stderr_tail"] = proc.stderr[-1500:]
    return row


def main() -> int:
    checks = [
        run("WEIGHTED_FINITE_SEARCH",
            [PY, "-I", "-B", str(HERE / "reference" / "search_bound.py"),
             "--n", "3", "--mult", "2", "--sink", "1", "--extra", "0"]),
        run("WEIGHTED_INDEPENDENT_CHECK",
            [PY, "-I", "-B", str(HERE / "independent" / "independent_check.py"), "3", "2", "1"]),
        run("WEIGHTED_WELLFOUNDED_EQUIVALENCE",
            [PY, "-I", "-B", str(HERE / "reference" / "equivalence.py"), "2"]),
        run("WEIGHTED_SINK_COLLAPSE",
            [PY, "-I", "-B", str(HERE / "reference" / "sink_collapse.py"), "2"]),
        run("WEIGHTED_LEAN_AUDIT",
            [PY, "-B", str(HERE / "lean" / "replay.py"), "--audit-only"]),
    ]

    gates: list[str] = []
    search = next(c for c in checks if c["id"] == "WEIGHTED_FINITE_SEARCH").get("result", {})
    if search:
        # Gate on the TRANSFER property, which is what the theorem asserts.
        # Nonconfluence is strictly weaker and is reported but not gated: a
        # capacity system can be confluent and still terminate away from the
        # ordinary normal form.
        control = search["transfer_control_C_eq_d"]["failing_systems"]
        candidate = search["candidate_bound"]["nonconfluent_systems"]
        sharp = search["transfer_sharpness_one_receiver_lowered"]["failing_systems"]
        if control <= 0:
            gates.append("transfer control found no failure at C=d (box is degenerate)")
        if candidate != 0:
            gates.append(f"candidate bound admitted {candidate} nonconfluent systems")
        if sharp <= 0:
            gates.append("sharpness sweep found no transfer failure one below the bound")
    else:
        gates.append("finite search produced no parsable result")

    ind = next(c for c in checks if c["id"] == "WEIGHTED_INDEPENDENT_CHECK").get("result", {})
    if ind:
        if ind["at_bound"]["terminal_disagreements"] != 0:
            gates.append("independent check disagreed at the bound")
        if ind["adverse_control_one_below_at_one_receiver"]["terminal_disagreements"] <= 0:
            gates.append("independent adverse control did not fail as required")
    else:
        gates.append("independent check produced no parsable result")

    # The well-foundedness reformulation (revision 0.5.0).  Run on the small box
    # so the bundled checks stay fast; the n<=3 run is a separate dossier check.
    eqv = next(c for c in checks if c["id"] == "WEIGHTED_WELLFOUNDED_EQUIVALENCE").get("result", {})
    if eqv:
        for gate, ok in eqv["gates"].items():
            if not ok:
                gates.append(f"well-foundedness gate failed: {gate}")
    else:
        gates.append("well-foundedness equivalence produced no parsable result")

    # The capacitated-sink collapse (revision 0.7.0), small box.
    sink = next(c for c in checks if c["id"] == "WEIGHTED_SINK_COLLAPSE").get("result", {})
    if sink:
        for gate, ok in sink["gates"].items():
            if not ok:
                gates.append(f"sink-collapse gate failed: {gate}")
    else:
        gates.append("sink-collapse check produced no parsable result")

    audit = next(c for c in checks if c["id"] == "WEIGHTED_LEAN_AUDIT").get("result", {})
    if not audit.get("no_escape"):
        gates.append("Lean source audit found a proof escape")

    out = {
        "schema": "cbmd.weighted-capacity-chipfiring-checks.v1",
        "status": "PASS" if all(c["status"] == "PASS" for c in checks) and not gates else "FAIL",
        "content_gate_failures": gates,
        "checks": checks,
        "nonclaims": [
            "Lean recompilation is not performed by this script",
            "finite enumeration corroborates the theorem and does not prove it",
            "no external independent verification and no novelty determination",
        ],
        "authority_effect": "NONE",
    }
    print(json.dumps(out, indent=1))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
