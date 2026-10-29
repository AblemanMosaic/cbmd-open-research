from __future__ import annotations

import platform
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .canonical import file_sha256, load_json, root, write_json
from .ledger import Ledger
from .refusals import Refusal


def _now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def recover_uncertain(root_path: Path, operation_id: str, basis: str) -> dict[str, Any]:
    if not operation_id or any(
        char not in "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.-" for char in operation_id
    ):
        raise Refusal("CBMD_OPERATION_ID_REFUSED", operation_id)
    allowed_bases = {
        "OWNED_PROCESS_NOT_OBSERVED_AFTER_CONTROLLED_INTERRUPT",
        "CONTROLLER_RETURNED_WITHOUT_TERMINAL_AND_NO_OWNED_PROCESS_OBSERVED",
    }
    if basis not in allowed_bases:
        raise Refusal("CBMD_RECOVERY_BASIS_REFUSED", basis)
    operation_dir = root_path / "runtime" / "operations" / operation_id
    intent_path = operation_dir / "INTENT.json"
    terminal_path = operation_dir / "TERMINAL.json"
    stdout_path = operation_dir / "stdout.bin"
    stderr_path = operation_dir / "stderr.bin"
    if not intent_path.is_file():
        raise Refusal("CBMD_RECOVERY_INTENT_MISSING", operation_id)
    if terminal_path.exists():
        from .evidence import verify_operation
        verify_operation(operation_dir)
        return load_json(terminal_path)
    if not stdout_path.is_file() or not stderr_path.is_file():
        raise Refusal("CBMD_RECOVERY_STREAM_MISSING", operation_id)
    intent = load_json(intent_path)
    intent_body = {key: value for key, value in intent.items() if key != "intent_root"}
    if root(intent_body) != intent.get("intent_root"):
        raise Refusal("CBMD_INTENT_ROOT_REFUSED", operation_id)

    semantic_terminal = {
        "schema": "cbmd.execution-terminal.v1",
        "operation_id": operation_id,
        "request_root": intent["request_root"],
        "intent_root": intent["intent_root"],
        "status": "UNOBSERVED",
        "timed_out": None,
        "interrupted": None,
        "exit_code": None,
        "stdout_root": file_sha256(stdout_path),
        "stderr_root": file_sha256(stderr_path),
        "outputs": [],
        "claim_boundary": intent["claim_boundary"],
        "known_remainder": [
            "Execution ended without contemporaneous terminal custody.",
            "No success, failure, theorem, or mathematical claim may rely on this operation.",
        ],
        "recovery": {
            "basis": basis,
            "epistemic_status": "PROCESS_RESULT_UNOBSERVED",
            "claim_eligible": False,
        },
        "authority_effect": "NONE",
    }
    terminal = dict(semantic_terminal)
    terminal["terminal_root"] = root(semantic_terminal)
    terminal["host_observation"] = {
        "recovered_at": _now(),
        "platform": platform.platform(),
        "python": platform.python_version(),
    }
    write_json(terminal_path, terminal)
    Ledger(root_path / "runtime" / "ledger").append(
        "EXECUTION_TERMINAL", operation_id, terminal["terminal_root"]
    )
    return terminal
