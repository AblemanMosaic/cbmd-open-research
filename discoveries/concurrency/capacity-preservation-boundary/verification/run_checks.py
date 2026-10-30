"""Bundled checks for the capacity-preservation boundary dossier.

Fast subset of the three censuses, with content gates: the chip-firing-shaped
translation must be exact, the relaxations must break it in the recorded way,
and the generalized conditions must be demonstrably unsound.
"""
from __future__ import annotations
import json, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import petri2, boundary, general

def main() -> int:
    translation = petri2.run(2, 2, 2, 3)
    relax = [boundary.run(r) for r in ("none", "selffeed", "shared", "multi_input")]
    gen = general.run(2, 2, 2, 2)
    gates = []
    if not translation["exact"]:
        gates.append("the chip-firing-shaped translation is no longer exact")
    if translation["chipfiring_shaped_systems"] == 0:
        gates.append("no chip-firing-shaped system was examined (degenerate box)")
    by = {r["relaxation"]: r for r in relax}
    if not by["none"]["exact"]:
        gates.append("control relaxation 'none' is not exact")
    if by["selffeed"]["UNSOUND"] != 0:
        gates.append("self-feedback produced an unsound case, contradicting the recorded finding")
    if by["selffeed"]["INCOMPLETE"] == 0:
        gates.append("self-feedback produced no incomplete case; the recorded asymmetry is absent")
    for r in ("shared", "multi_input"):
        if by[r]["UNSOUND"] == 0:
            gates.append(f"relaxation '{r}' produced no unsound case; load-bearing claim unsupported")
    if gen["UNSOUND"] == 0:
        gates.append("the generalized conditions were not shown unsound")
    out = {"schema": "cbmd.capacity-preservation-boundary-checks.v1",
           "chipfiring_translation": translation,
           "relaxation_boundary": relax,
           "generalized_conditions": gen,
           "content_gate_failures": gates,
           "status": "PASS" if not gates else "FAIL",
           "nonclaims": [
               "finite censuses over the stated boxes; no unbounded theorem is established here",
               "the chip-firing characterization itself is proved in CBMD-DYN-WEIGHTED-CAPACITY-001; this dossier only maps where it transfers",
               "no claim that NO local capacity condition can repair the multi-input case",
           ],
           "authority_effect": "NONE"}
    print(json.dumps(out, indent=1))
    return 0 if not gates else 1

if __name__ == "__main__":
    raise SystemExit(main())
