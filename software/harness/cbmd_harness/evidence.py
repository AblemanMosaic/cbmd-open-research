from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .canonical import file_sha256, load_json, root
from .contracts import load_and_verify_specs
from .ledger import Ledger
from .refusals import Refusal


def _mathematical_adverse_receipt(root_path: Path) -> tuple[bool, str]:
    receipt_path = root_path / "evidence" / "MATHEMATICAL_ADVERSE_RECEIPT.json"
    if not receipt_path.is_file():
        return False, "No qualified mathematical-adapter mutation receipt is present."
    try:
        receipt = load_json(receipt_path)
        controls = receipt["mutant_controls"]
        if receipt.get("schema") != "cbmd.mathematical-adverse-receipt.v1" or receipt.get("status") != "PASS":
            return False, "The mathematical-adapter mutation receipt has the wrong schema or standing."
        if len(controls) < 2 or any(not isinstance(item.get("detections"), int) or item["detections"] <= 0 for item in controls):
            return False, "The mathematical-adapter mutation receipt lacks positive detections for two controls."
        operation_dir = root_path / "runtime" / "operations" / receipt["operation_id"]
        if not operation_dir.is_dir():
            return False, "The mathematical-adapter receipt has no local operation custody."
        terminal = verify_operation(operation_dir)
        if terminal.get("status") != "PASS" or terminal.get("terminal_root") != receipt.get("terminal_root"):
            return False, "The mathematical-adapter mutation receipt does not match terminal custody."
    except (KeyError, TypeError, Refusal):
        return False, "The mathematical-adapter mutation receipt is malformed or conflicts with terminal custody."
    return True, "Mathematical mutation coverage is bounded by the declared finite audit and its local operation custody."


def verify_operation(operation_dir: Path) -> dict[str, Any]:
    intent_path = operation_dir / "INTENT.json"
    terminal_path = operation_dir / "TERMINAL.json"
    if not intent_path.is_file():
        raise Refusal("CBMD_OPERATION_INTENT_MISSING", operation_dir.name)
    intent = load_json(intent_path)
    intent_body = {key: value for key, value in intent.items() if key != "intent_root"}
    if root(intent_body) != intent.get("intent_root"):
        raise Refusal("CBMD_INTENT_ROOT_REFUSED", operation_dir.name)
    if not terminal_path.exists():
        return {"operation_id": operation_dir.name, "status": "UNCERTAIN", "intent_root": intent["intent_root"]}
    terminal = load_json(terminal_path)
    terminal_body = {key: value for key, value in terminal.items() if key not in {"terminal_root", "host_observation"}}
    if root(terminal_body) != terminal.get("terminal_root"):
        raise Refusal("CBMD_TERMINAL_ROOT_REFUSED", operation_dir.name)
    if terminal["intent_root"] != intent["intent_root"]:
        raise Refusal("CBMD_INTENT_TERMINAL_MISMATCH", operation_dir.name)
    if intent["operation_id"] != operation_dir.name or terminal["operation_id"] != operation_dir.name:
        raise Refusal("CBMD_OPERATION_IDENTITY_MISMATCH", operation_dir.name)
    if terminal["request_root"] != intent["request_root"]:
        raise Refusal("CBMD_REQUEST_TERMINAL_MISMATCH", operation_dir.name)
    if file_sha256(operation_dir / "stdout.bin") != terminal["stdout_root"]:
        raise Refusal("CBMD_STDOUT_ROOT_REFUSED", operation_dir.name)
    if file_sha256(operation_dir / "stderr.bin") != terminal["stderr_root"]:
        raise Refusal("CBMD_STDERR_ROOT_REFUSED", operation_dir.name)
    return {"operation_id": operation_dir.name, "status": terminal["status"],
            "intent_root": intent["intent_root"], "terminal_root": terminal["terminal_root"]}


def verify_all(root_path: Path) -> dict[str, Any]:
    spec_roots = load_and_verify_specs(root_path)
    ledger = Ledger(root_path / "runtime" / "ledger")
    ledger_state = ledger.verify()
    events = []
    if ledger.journal.is_file():
        events = [json.loads(line) for line in ledger.journal.read_text(encoding="utf-8").splitlines()]
    operations_root = root_path / "runtime" / "operations"
    operations: list[dict[str, Any]] = []
    if operations_root.exists():
        for operation_dir in sorted(path for path in operations_root.iterdir() if path.is_dir()):
            operations.append(verify_operation(operation_dir))
    for operation in operations:
        intent_events = [event for event in events if event["event_type"] == "EXECUTION_INTENT"
                         and event["operation_id"] == operation["operation_id"]]
        if len(intent_events) != 1 or intent_events[0]["payload_root"] != operation["intent_root"]:
            raise Refusal("CBMD_LEDGER_INTENT_BINDING_REFUSED", operation["operation_id"])
        terminal_events = [event for event in events if event["event_type"] == "EXECUTION_TERMINAL"
                           and event["operation_id"] == operation["operation_id"]]
        if operation["status"] != "UNCERTAIN":
            if len(terminal_events) != 1 or terminal_events[0]["payload_root"] != operation["terminal_root"]:
                raise Refusal("CBMD_LEDGER_TERMINAL_BINDING_REFUSED", operation["operation_id"])
            if terminal_events[0]["sequence"] <= intent_events[0]["sequence"]:
                raise Refusal("CBMD_LEDGER_EXECUTION_ORDER_REFUSED", operation["operation_id"])
        elif terminal_events:
            raise Refusal("CBMD_LEDGER_TERMINAL_CUSTODY_MISSING", operation["operation_id"])
    operation_ids = {item["operation_id"] for item in operations}
    if any(event["event_type"] in {"EXECUTION_INTENT", "EXECUTION_TERMINAL"}
           and event["operation_id"] not in operation_ids for event in events):
        raise Refusal("CBMD_LEDGER_OPERATION_MISSING", "recorded execution has no operation directory")
    uncertain = [item["operation_id"] for item in operations if item["status"] == "UNCERTAIN"]
    status = "PASS" if not uncertain else "DEGRADED"
    return {
        "schema": "cbmd.evidence-verification.v1",
        "status": status,
        "authority_effect": "NONE",
        **spec_roots,
        "ledger": ledger_state,
        "operations": operations,
        "uncertain_operations": uncertain,
        "claim_boundary": "SELF_VERIFICATION_NOT_INDEPENDENT",
    }


def health(root_path: Path) -> dict[str, Any]:
    checks: dict[str, str] = {}
    remainder: list[str] = []
    try:
        verification = verify_all(root_path)
        checks["AUTHORITY_SCOPE_VISIBLE"] = "HEALTHY"
        checks["IDENTITIES_BOUND"] = "HEALTHY"
        checks["CHAIN_CONTINUITY"] = "HEALTHY"
        checks["REFUSAL_VISIBILITY"] = "HEALTHY"
        observed = bool(verification["operations"])
        checks["INTENT_BEFORE_EXECUTION"] = "HEALTHY" if observed else "UNOBSERVED"
        checks["TERMINAL_CUSTODY"] = ("DEGRADED" if verification["uncertain_operations"] else "HEALTHY") if observed else "UNOBSERVED"
        checks["STDOUT_STDERR_EXIT_CAPTURED"] = "HEALTHY" if observed else "UNOBSERVED"
        if not observed:
            remainder.append("This workspace has no recorded operations; process evidence is unobserved.")
    except (Refusal, OSError, ValueError, KeyError, TypeError) as exc:
        checks["CHAIN_CONTINUITY"] = "CONFLICT"
        remainder.append(f"{exc.code}:{exc.detail}" if isinstance(exc, Refusal) else f"{type(exc).__name__}:{exc}")
    for dimension in ("AUTHORITY_SCOPE_VISIBLE", "IDENTITIES_BOUND", "REFUSAL_VISIBILITY",
                      "INTENT_BEFORE_EXECUTION", "TERMINAL_CUSTODY", "STDOUT_STDERR_EXIT_CAPTURED"):
        checks.setdefault(dimension, "UNOBSERVED")
    checks.setdefault("SOURCE_CORRESPONDENCE", "GAP")
    adverse_healthy, adverse_scope = _mathematical_adverse_receipt(root_path)
    checks["ADVERSE_COVERAGE"] = "HEALTHY" if adverse_healthy else "UNOBSERVED"
    checks["INDEPENDENCE_DISCLOSURE"] = "HEALTHY"
    checks["CLAIM_CEILING_ENFORCED"] = "HEALTHY"
    checks["KNOWN_REMAINDER_VISIBLE"] = "HEALTHY"
    remainder.extend([
        "UCM native proof adapter is not yet bound.",
        adverse_scope,
        "No external independent verifier has qualified this harness.",
    ])
    healthy = sum(value == "HEALTHY" for value in checks.values())
    conflicts = any(value == "CONFLICT" for value in checks.values())
    status = "CONFLICT" if conflicts else ("HEALTHY" if healthy == len(checks) else "DEGRADED")
    return {
        "schema": "cbmd.evidence-health.v1",
        "profile_id": "CBMD.MAX_DIAGNOSTIC.V1",
        "status": status,
        "numerator": healthy,
        "denominator": len(checks),
        "dimensions": checks,
        "known_remainder": remainder,
        "common_mode_limits": ["Harness, ledger verifier, and health projection share one codebase."],
        "esa": {
            "epistemic_act_recognition": "IMPLEMENTED_CANDIDATE",
            "authority_projection": "IMPLEMENTED_CANDIDATE",
            "stopping_recognition": "IMPLEMENTED_CANDIDATE",
            "nonclaim": "Engineering control property; not consciousness, confidence, or omniscience."
        },
        "authority_effect": "NONE",
    }
