"""Bundled checks for the fixed-state dossier (standard library only)."""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def run(name, cmd):
    p = subprocess.run(cmd, cwd=HERE, capture_output=True, text=True)
    row = {"id": name, "exit_code": p.returncode, "status": "PASS" if p.returncode == 0 else "FAIL"}
    try:
        row["result"] = json.loads(p.stdout)
    except json.JSONDecodeError:
        row["stdout_tail"] = p.stdout[-1500:]
        row["stderr_tail"] = p.stderr[-1500:]
    return row


def main():
    checks = [
        run("STAR_REDUCTION", [sys.executable, "-I", "-B", str(HERE / "reference" / "star_reduction.py"), "1200"]),
        run("RESIDUE_WITNESS", [sys.executable, "-I", "-B", str(HERE / "reference" / "residue_witness.py"),
                                "20261030", "10", "6"]),
        run("SEMANTICS_CUSTODY", [sys.executable, "-I", "-B", str(HERE / "semantics_custody.py")]),
        run("LEAN_AUDIT", [sys.executable, "-B", str(HERE / "lean" / "replay.py"), "--audit-only"]),
    ]
    gates = []
    for c in checks:
        res = c.get("result", {})
        if c["status"] != "PASS":
            gates.append(f"{c['id']} failed")
        for g, ok in res.get("gates", {}).items():
            if not ok:
                gates.append(f"{c['id']} gate failed: {g}")
    audit = next(c for c in checks if c["id"] == "LEAN_AUDIT").get("result", {})
    if not audit.get("no_escape"):
        gates.append("Lean source audit found a proof escape")
    out = {"schema": "cbmd.fixed-state-checks.v1",
           "status": "PASS" if not gates else "FAIL", "content_gate_failures": gates,
           "checks": checks,
           "nonclaims": ["Lean recompilation is not performed here; use lean/replay.py --build",
                         "the NP-hardness of 3-PARTITION is classical and cited, not proved",
                         "the residue-witness converse is a conjecture checked exhaustively in range, not proved; the bundled run uses B <= 10, k <= 6 and evidence/residue_witness.json records B <= 13, k <= 8"],
           "authority_effect": "NONE"}
    print(json.dumps(out, indent=1))
    return 0 if out["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
