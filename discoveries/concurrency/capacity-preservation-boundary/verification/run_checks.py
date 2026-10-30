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
import petri2, boundary, general, allfull, flow, hardness, weighted_flow, single_input, backdoor, reduction_bridge

def main() -> int:
    translation = petri2.run(2, 2, 2, 3)
    relax = [boundary.run(r) for r in ("none", "selffeed", "shared", "multi_input")]
    gen = general.run(2, 2, 2, 2)
    af = allfull.run()
    fl = flow.run()
    hd = hardness.run(trials=80)
    hd["exhaustive"] = hardness.exhaustive()
    hd["gates"].update(hd["exhaustive"]["gates"])
    wf = weighted_flow.report()
    si = single_input.run()
    bd = backdoor.run()
    rb = reduction_bridge.run()
    gates = []
    for gate, ok in rb["gates"].items():
        if not ok:
            gates.append(f"reduction bridge gate failed: {gate}")
    for gate, ok in bd["gates"].items():
        if not ok:
            gates.append(f"backdoor gate failed: {gate}")
    for gate, ok in si["gates"].items():
        if not ok:
            gates.append(f"single-input gate failed: {gate}")
    for gate, ok in wf["gates"].items():
        if not ok:
            gates.append(f"weighted flow gate failed: {gate}")
    for gate, ok in hd["gates"].items():
        if not ok:
            gates.append(f"hardness reduction gate failed: {gate}")
    for gate, ok in fl["gates"].items():
        if not ok:
            gates.append(f"flow characterization gate failed: {gate}")
    for gate, ok in af["gates"].items():
        if not ok:
            gates.append(f"all-full obstruction gate failed: {gate}")
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
    audit = json.loads(__import__("subprocess").run(
        [sys.executable, "-B", str(HERE / "lean" / "replay.py"), "--audit-only"],
        capture_output=True, text=True).stdout or "{}")
    if not audit.get("no_escape"):
        gates.append("Lean source audit found a proof escape")
    out = {"schema": "cbmd.capacity-preservation-boundary-checks.v1",
           "chipfiring_translation": translation,
           "relaxation_boundary": relax,
           "generalized_conditions": gen,
           "allfull_obstruction": af,
           "flow_characterization": fl,
           "hardness_reduction": hd,
           "weighted_flow": wf,
           "single_input": si,
           "backdoor": bd,
           "reduction_bridge": rb,
           "content_gate_failures": gates,
           "status": "PASS" if not gates else "FAIL",
           "nonclaims": [
               "finite censuses over the stated boxes; no unbounded theorem is established here",
               "the chip-firing characterization itself is proved in CBMD-DYN-WEIGHTED-CAPACITY-001; this dossier only maps where it transfers",
               "no claim that NO local capacity condition can repair the multi-input case",
               "the all-full obstruction is proved in verification/lean/; the census here corroborates it and is not the proof",
               "the coNP-completeness statement is a written argument; only the correctness of the reduction is machine checked",
           ],
           "authority_effect": "NONE"}
    print(json.dumps(out, indent=1))
    return 0 if not gates else 1

if __name__ == "__main__":
    raise SystemExit(main())
