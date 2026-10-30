"""The copied semantics are the weighted dossier's semantics, verbatim.

`lean/CBMDFixedState/Semantics.lean` copies the definitions of the
capacity-blocked chip-firing model from CBMD-DYN-WEIGHTED-CAPACITY-001, so
that the fixed-state theorems are about exactly the model characterized there.
This check extracts each copied declaration and the same-named declaration in
the weighted sources, normalizes whitespace, and requires them to be identical.
A copy that drifted would make the two dossiers talk about different models.
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
COPY = HERE / "lean" / "CBMDFixedState" / "Semantics.lean"
WSRC = HERE.parents[1] / "weighted-capacity-chip-firing" / "verification" / "lean" / "CBMDWeightedDynamics"
NAMES = ["Vertex", "Chips", "OrdinaryUnstable", "OrdinaryStable", "ReceiverBlocked",
         "CapacityLegal", "CapacityTerminal", "CapacityStep", "Reaches", "wFire"]


def strip_comments(t: str) -> str:
    return re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", t, flags=re.S))


def declaration(text: str, name: str):
    text = strip_comments(text)
    m = re.search(rf"^(abbrev|def|inductive) {re.escape(name)}\b.*?(?=^\S|\Z)", text, re.M | re.S)
    return None if m is None else " ".join(m.group(0).split())


def run():
    copy = COPY.read_text(encoding="utf-8")
    weighted = "\n".join(p.read_text(encoding="utf-8") for p in sorted(WSRC.glob("*.lean")))
    rows = []
    for name in NAMES:
        c, w = declaration(copy, name), declaration(weighted, name)
        rows.append({"name": name, "found_in_copy": c is not None, "found_in_weighted": w is not None,
                     "identical": c is not None and c == w})
    # control: a one-symbol change to a copied definition must be detected
    mutated = copy.replace("outdegree v ≤ chips v", "outdegree v < chips v")
    control_detected = declaration(mutated, "OrdinaryUnstable") != declaration(weighted, "OrdinaryUnstable")
    ok = all(r["identical"] for r in rows) and control_detected
    return {"schema": "cbmd.fixed-state-semantics-custody.v1", "declarations": rows,
            "mutation_control_detected": control_detected,
            "status": "PASS" if ok else "FAIL", "authority_effect": "NONE"}


if __name__ == "__main__":
    out = run()
    print(json.dumps(out, indent=1))
    raise SystemExit(0 if out["status"] == "PASS" else 1)
