from __future__ import annotations

import os
import platform
import shutil
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from .canonical import file_sha256, load_json, root, write_json
from .contracts import load_and_verify_specs, require_exact_keys
from .ledger import Ledger
from .refusals import Refusal


REQUEST_KEYS = {
    "schema", "operation_id", "question_id", "claim_ids", "runner_id", "argv", "cwd",
    "environment_delta", "timeout_seconds", "expected_exit_codes", "inputs", "outputs",
    "claim_boundary", "known_remainder", "authority_id",
}


def _now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def _resolve_executable(name: str, cwd: Path) -> Path:
    candidate = Path(name)
    if candidate.is_absolute():
        resolved = candidate.resolve(strict=True)
    elif len(candidate.parts) > 1:
        resolved = (cwd / candidate).resolve(strict=True)
    else:
        found = shutil.which(name)
        if not found:
            raise Refusal("CBMD_EXECUTABLE_NOT_FOUND", name)
        resolved = Path(found).resolve(strict=True)
    if not resolved.is_file():
        raise Refusal("CBMD_EXECUTABLE_REFUSED", str(resolved))
    return resolved


def validate_request(request: dict[str, Any]) -> None:
    require_exact_keys(request, REQUEST_KEYS, set(), "run_request")
    if request["schema"] != "cbmd.run-request.v1":
        raise Refusal("CBMD_RUN_SCHEMA_REFUSED", str(request["schema"]))
    if not isinstance(request["operation_id"], str) or not request["operation_id"] or any(char not in "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.-" for char in request["operation_id"]):
        raise Refusal("CBMD_OPERATION_ID_REFUSED", str(request["operation_id"]))
    if not isinstance(request["argv"], list) or not request["argv"] or not all(isinstance(x, str) and x for x in request["argv"]):
        raise Refusal("CBMD_ARGV_REFUSED", "argv must be a non-empty string array")
    if not isinstance(request["timeout_seconds"], int) or isinstance(request["timeout_seconds"], bool) or request["timeout_seconds"] < 1:
        raise Refusal("CBMD_TIMEOUT_REFUSED", "positive integer required")
    if not isinstance(request["expected_exit_codes"], list) or not request["expected_exit_codes"]:
        raise Refusal("CBMD_EXIT_POLICY_REFUSED", "expected_exit_codes")
    forbidden_fragments = ("TOKEN", "SECRET", "PASSWORD", "CREDENTIAL", "PRIVATE_KEY")
    for key, value in request["environment_delta"].items():
        if any(fragment in key.upper() for fragment in forbidden_fragments):
            raise Refusal("CBMD_SECRET_ENV_REFUSED", key)
        if not isinstance(value, str):
            raise Refusal("CBMD_ENV_VALUE_REFUSED", key)


def _verify_inputs(inputs: list[dict[str, str]]) -> list[dict[str, str]]:
    verified: list[dict[str, str]] = []
    seen: set[str] = set()
    for item in inputs:
        require_exact_keys(item, {"path", "sha256", "role"}, set(), "input")
        path = Path(item["path"]).resolve(strict=True)
        identity = str(path).casefold()
        if identity in seen:
            raise Refusal("CBMD_INPUT_DUPLICATE", str(path))
        seen.add(identity)
        actual = file_sha256(path)
        if actual != item["sha256"]:
            raise Refusal("CBMD_INPUT_DRIFT", str(path))
        verified.append({"path_identity": root({"path": str(path)}), "sha256": actual, "role": item["role"]})
    return verified


def execute(root_path: Path, request_path: Path) -> dict[str, Any]:
    request = load_json(request_path)
    validate_request(request)
    request_root = root(request)
    operation_id = request["operation_id"]
    operation_dir = root_path / "runtime" / "operations" / operation_id
    intent_path = operation_dir / "INTENT.json"
    terminal_path = operation_dir / "TERMINAL.json"
    ledger = Ledger(root_path / "runtime" / "ledger")
    if terminal_path.exists():
        terminal = load_json(terminal_path)
        if terminal["request_root"] != request_root:
            raise Refusal("CBMD_OPERATION_ID_CONFLICT", operation_id)
        from .evidence import verify_all
        verify_all(root_path)
        return terminal
    if intent_path.exists():
        intent = load_json(intent_path)
        if intent["request_root"] != request_root:
            raise Refusal("CBMD_OPERATION_ID_CONFLICT", operation_id)
        raise Refusal("CBMD_OPERATION_UNCERTAIN", operation_id)

    spec_roots = load_and_verify_specs(root_path)
    authority = load_json(root_path / "spec" / "CBMD-AUTHORITY.json")
    if request["authority_id"] != authority["authority_id"]:
        raise Refusal("CBMD_AUTHORITY_ID_REFUSED", request["authority_id"])
    if "LOCAL_TOOL_EXECUTION" not in authority["allowed_effects"]:
        raise Refusal("CBMD_LOCAL_EXECUTION_REFUSED", "local tool execution is not enabled")
    cwd = Path(request["cwd"]).resolve(strict=True)
    if not cwd.is_dir():
        raise Refusal("CBMD_CWD_REFUSED", str(cwd))
    allowed_roots = [Path(item).resolve(strict=True) for item in authority["allowed_execution_roots"]]
    if not any(cwd == allowed or allowed in cwd.parents for allowed in allowed_roots):
        raise Refusal("CBMD_EXECUTION_ROOT_REFUSED", str(cwd))
    executable = _resolve_executable(request["argv"][0], cwd)
    verified_inputs = _verify_inputs(request["inputs"])
    executable_record = {"path_identity": root({"path": str(executable)}), "sha256": file_sha256(executable)}
    semantic_intent = {
        "schema": "cbmd.execution-intent.v1",
        "operation_id": operation_id,
        "request_root": request_root,
        "governing_contract_roots": spec_roots,
        "runner_id": request["runner_id"],
        "executable": executable_record,
        "argv": request["argv"],
        "cwd_identity": root({"path": str(cwd)}),
        "environment_delta": request["environment_delta"],
        "inputs": verified_inputs,
        "authority_id": request["authority_id"],
        "claim_boundary": request["claim_boundary"],
    }
    intent = dict(semantic_intent)
    intent["intent_root"] = root(semantic_intent)
    operation_dir.mkdir(parents=True, exist_ok=False)
    write_json(intent_path, intent)
    ledger.append("EXECUTION_INTENT", operation_id, intent["intent_root"])

    stdout_path = operation_dir / "stdout.bin"
    stderr_path = operation_dir / "stderr.bin"
    environment = dict(os.environ)
    environment.update(request["environment_delta"])
    started_at = _now()
    start = time.monotonic()
    timed_out = False
    interrupted = False
    launch_error: dict[str, Any] | None = None
    exit_code: int | None = None
    invocation = [str(executable), *request["argv"][1:]]
    with stdout_path.open("wb") as stdout_handle, stderr_path.open("wb") as stderr_handle:
        try:
            process = subprocess.Popen(
                invocation, cwd=cwd, env=environment, stdin=subprocess.DEVNULL,
                stdout=stdout_handle, stderr=stderr_handle, shell=False,
            )
        except OSError as exc:
            launch_error = {"kind": type(exc).__name__, "errno": exc.errno}
            stderr_handle.write((str(exc) + "\n").encode("utf-8"))
        else:
            try:
                exit_code = process.wait(timeout=request["timeout_seconds"])
            except subprocess.TimeoutExpired:
                timed_out = True
                process.kill()
                exit_code = process.wait()
            except KeyboardInterrupt:
                interrupted = True
                if process.poll() is None:
                    process.kill()
                exit_code = process.wait()
    elapsed_ms = int((time.monotonic() - start) * 1000)
    finished_at = _now()

    outputs: list[dict[str, Any]] = []
    for output in request["outputs"]:
        require_exact_keys(output, {"path", "required", "role"}, set(), "output")
        path = Path(output["path"])
        if not path.is_absolute():
            path = cwd / path
        path = path.resolve(strict=False)
        present = path.is_file()
        if output["required"] and not present:
            outputs.append({"path_identity": root({"path": str(path)}), "role": output["role"], "present": False})
        elif present:
            outputs.append({"path_identity": root({"path": str(path)}), "role": output["role"], "present": True, "sha256": file_sha256(path)})
        else:
            outputs.append({"path_identity": root({"path": str(path)}), "role": output["role"], "present": False})

    status = (
        "ABORTED" if interrupted else
        ("PASS" if launch_error is None and not timed_out and exit_code in request["expected_exit_codes"] else "FAIL")
    )
    if any(output["required"] and not record["present"] for output, record in zip(request["outputs"], outputs)):
        status = "FAIL"
    semantic_terminal = {
        "schema": "cbmd.execution-terminal.v1",
        "operation_id": operation_id,
        "request_root": request_root,
        "intent_root": intent["intent_root"],
        "status": status,
        "timed_out": timed_out,
        "interrupted": interrupted,
        "exit_code": exit_code,
        "launch_error": launch_error,
        "stdout_root": file_sha256(stdout_path),
        "stderr_root": file_sha256(stderr_path),
        "outputs": outputs,
        "claim_boundary": request["claim_boundary"],
        "known_remainder": request["known_remainder"],
        "authority_effect": "NONE",
    }
    terminal = dict(semantic_terminal)
    terminal["terminal_root"] = root(semantic_terminal)
    terminal["host_observation"] = {
        "started_at": started_at,
        "finished_at": finished_at,
        "elapsed_ms": elapsed_ms,
        "platform": platform.platform(),
        "python": platform.python_version(),
    }
    write_json(terminal_path, terminal)
    ledger.append("EXECUTION_TERMINAL", operation_id, terminal["terminal_root"])
    return terminal
