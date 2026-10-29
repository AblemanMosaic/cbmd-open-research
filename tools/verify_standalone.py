"""Deterministic finite exact audit of the public stdlib reference toolkit.

Run from a clean checkout, offline, with Python >=3.10.  This verifier imports
neither owner_sum.py nor a frozen producer.  Its oracles are separately coded
within the project; that is not external independent verification.  No Lean
theorem is certified by running this Python audit.
"""

from __future__ import annotations

from dataclasses import asdict
import hashlib
from itertools import product
import json
from math import comb
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "software" / "reference"))

from cbmd_reference import (  # noqa: E402
    BCM1Counts, UniversalState, active_set, joint_entry, master_numerator,
    mismatches, orbit_compatible,
)
from cbmd_reference.oracle import (  # noqa: E402
    formula_oracle, integer_choose, interpolation_oracle, native_entry_oracle,
    orbit_oracle,
)


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")


def require(condition: bool, diagnostic: object) -> None:
    if not condition:
        raise ValueError(str(diagnostic))


def _ordinary_mutant(a: int, r: int, delta: int, f: int) -> int:
    degree = r - 1 - f
    upper = a + r - delta
    total = sum(
        (1 if k == 0 else comb(upper, k) if upper >= 0 and k <= upper else 0)
        * comb(max(a + degree - k - 1, 0), degree - k)
        for k in range(degree + 1)
    )
    return (-1) ** a * 2 ** (r - 1) * total


def _states(q: int, slots: int) -> list[UniversalState]:
    return [
        UniversalState(tuple(flat[:q]), tuple(
            tuple(flat[(j + 1) * q:(j + 2) * q]) for j in range(slots)))
        for flat in product((0, 1), repeat=q * (slots + 1))
    ]


def verify() -> dict[str, object]:
    inputs = hashlib.sha256()
    values = hashlib.sha256()
    counts = {name: 0 for name in (
        "scalar", "interpolation", "orbit", "native_joint", "A_zero", "R_one",
        "negative_upper", "m_zero", "zero_outside_orbit", "zero_above_support",
        "centered_vanishing", "A_zero_offdiagonal_collapse",
    )}
    detection = {name: 0 for name in (
        "missing_A_sign", "missing_f_sign", "delta_off_by_one", "missing_scale",
        "ordinary_binomial_at_negative_upper", "mismatch_instead_of_active",
        "orbit_ignores_other_slots", "orbit_ignores_selected_slot",
        "support_rejects_equality",
    )}
    witnesses: dict[str, dict[str, object]] = {}

    def record(kind: str, data: object, expected: object) -> None:
        inputs.update(canonical([kind, data]) + b"\n")
        values.update(canonical([kind, data, expected]) + b"\n")

    def adverse(name: str, data: object, expected: object, mutant: object) -> None:
        if expected != mutant:
            detection[name] += 1
            witnesses.setdefault(name, {"input": data, "expected": expected, "mutant": mutant})

    cases = [
        (a, r, delta, f)
        for a in range(9) for r in range(1, 9)
        for delta in range(22) for f in range(r)
    ] + [(17, 5, 39, 0), (17, 5, 39, 2), (15, 8, 38, 3)]
    for a, r, delta, f in cases:
        data = {"A": a, "R": r, "delta": delta, "f": f}
        result = master_numerator(a, r, delta, f)
        expected = formula_oracle(a, r, delta, f)
        degree = r - 1 - f
        require(result.value == expected, ["scalar mismatch", data, asdict(result), expected])
        require(result.counts == BCM1Counts(3 * degree + 2, 2 * degree, degree + 1),
                ["BCM1 charge mismatch", data, asdict(result.counts)])
        require(result.choose_table == tuple(integer_choose(a + r - delta, k)
                                             for k in range(degree + 1)), data)
        counts["scalar"] += 1
        counts["A_zero"] += int(a == 0)
        counts["R_one"] += int(r == 1)
        counts["negative_upper"] += int(a + r - delta < 0)
        record("scalar", data, [expected, asdict(result.counts)])
        adverse("missing_A_sign", data, expected, (-1) ** a * expected)
        adverse("delta_off_by_one", data, expected, formula_oracle(a, r, delta + 1, f))
        adverse("missing_scale", data, expected, expected // 2 ** (r - 1))
        if a + r - delta < 0:
            adverse("ordinary_binomial_at_negative_upper", data, expected,
                    _ordinary_mutant(a, r, delta, f))
        if delta == 2 * a + r and f % 2 == r % 2:
            require(expected == 0, ["centered parity vanishing", data, expected])
            counts["centered_vanishing"] += 1

    for a in range(9):
        for r in range(1, 9):
            for f in range(r):
                for m in range(13):
                    data = {"A": a, "R": r, "f": f, "m": m}
                    expected = interpolation_oracle(a, r, f, m)
                    require(master_numerator(a, r, f + m + 1, f).value == expected, data)
                    record("interpolation", data, expected)
                    counts["interpolation"] += 1
                    counts["m_zero"] += int(m == 0)
                    adverse("missing_f_sign", data, expected, (-1) ** f * expected)

    # Exhaustive state pairs in these declared small binary spaces.  Two slots
    # are necessary to test the unselected-slot clause of orbit compatibility.
    shapes = [(q, 1) for q in range(1, 4)] + [(1, 2), (2, 2)]
    for q, slots in shapes:
        states = _states(q, slots)
        for u, y in product(states, repeat=2):
            state_data = {"i": 0, "u": asdict(u), "y": asdict(y)}
            expected_orbit = orbit_oracle(0, u, y)
            actual_orbit = orbit_compatible(0, u, y)
            require(actual_orbit == expected_orbit, ["orbit mismatch", state_data])
            record("orbit", state_data, expected_orbit)
            counts["orbit"] += 1
            pair_only = all((y.head[l], y.slots[0][l]) in (
                (u.head[l], u.slots[0][l]), (u.slots[0][l], u.head[l])) for l in range(q))
            adverse("orbit_ignores_other_slots", state_data, expected_orbit, pair_only)
            head_only = all(y.head[l] in (u.head[l], u.slots[0][l]) for l in range(q))
            head_only = head_only and u.slots[1:] == y.slots[1:]
            adverse("orbit_ignores_selected_slot", state_data, expected_orbit, head_only)
            # Common Joint(t=0,g=0,i=0); all pairs in each such fiber are tested.
            if not (u.head[0] == y.head[0] == 0 and u.slots[0][0] == y.slots[0][0] == 1):
                continue
            for a in range(3):
                for r in range(1, 4):
                    data = {**state_data, "t": 0, "A": a, "R": r}
                    expected = native_entry_oracle(0, 0, a, r, u, y)
                    result = joint_entry(0, 0, a, r, u, y)
                    require(result.value == expected, ["native mismatch", data, expected, asdict(result)])
                    record("native_joint", data, [expected, result.branch])
                    counts["native_joint"] += 1
                    mismatch_count = len(mismatches(0, u, y))
                    active_count = len(active_set(0, u))
                    if result.branch == "OUTSIDE_ORBIT":
                        require(expected == 0 and result.counts == BCM1Counts(), data)
                        counts["zero_outside_orbit"] += 1
                    elif result.branch == "ABOVE_MISMATCH_SUPPORT":
                        require(expected == 0 and result.counts == BCM1Counts(), data)
                        counts["zero_above_support"] += 1
                    else:
                        adverse("mismatch_instead_of_active", data, expected,
                                formula_oracle(a, r, mismatch_count, mismatch_count - 1))
                        if mismatch_count == r:
                            adverse("support_rejects_equality", data, expected, 0)
                    if a == 0 and expected_orbit and u != y and active_count <= r:
                        require(expected == 0, ["A=0 offdiagonal collapse", data, expected])
                        counts["A_zero_offdiagonal_collapse"] += 1

    require(all(detection.values()), ["undetected mutants", detection])
    require(all(counts.values()), ["unexercised boundary or branch", counts])
    source_files = sorted((ROOT / "software" / "reference").rglob("*.py")) + [Path(__file__)]
    return {
        "schema": "cbmd.reference.finite-audit.v1",
        "status": "PASS",
        "claim_boundary": "FINITE_EXACT_AUDIT_OF_PROJECT_AUTHORED_PYTHON",
        "case_plan": {
            "scalar": "A=0..8,R=1..8,delta=0..21,f=0..R-1; three high-negative-upper extras",
            "interpolation": "A=0..8,R=1..8,f=0..R-1,m=0..12",
            "binary_state_shapes_Q_slots": shapes,
            "joint": "all pairs in Joint(t=0,g=0,i=0) for each shape; A=0..2,R=1..3",
        },
        "case_counts": counts,
        "input_sha256": inputs.hexdigest(),
        "value_sha256": values.hexdigest(),
        "code_sha256": {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                        for path in source_files},
        "mutant_detections": detection,
        "first_mutant_witnesses": witnesses,
        "count_scope": "BCM1_SCALAR_ARITHMETIC_ONLY; both recurrence tables charged even at A=0",
        "nonclaims": [
            "LEAN_PROOF_REPLAY", "PYTHON_FORMAL_VERIFICATION", "EXTERNAL_INDEPENDENT_REVIEW",
            "COMPARISON_OR_MEMORY_OR_BIT_COST", "TOTAL_NATIVE_SPEEDUP", "SAT_ASYMPTOTIC_IMPROVEMENT",
            "NOVELTY", "GEOMETRIC_ECH_TRANSPORT",
        ],
    }


if __name__ == "__main__":
    print(json.dumps(verify(), sort_keys=True, separators=(",", ":")))
