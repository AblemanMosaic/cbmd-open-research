from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from cbmd_harness.adapters import plan_python
from cbmd_harness.canonical import load_json, root, write_json
from cbmd_harness.evidence import health, verify_all
from cbmd_harness.ledger import Ledger
from cbmd_harness.promotion import decide_promotion
from cbmd_harness.refusals import Refusal
from cbmd_harness.runner import execute
from cbmd_harness.workspace import initialize_workspace


ROOT = Path(__file__).resolve().parent.parent


class PortableTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.base = Path(self.temporary.name)
        self.project = self.base / "project"
        self.project.mkdir()
        self.workspace = self.base / "workspace"
        self.script = self.project / "probe.py"
        self.script.write_text("print(6 * 7)\n", encoding="utf-8")

    def configured(self) -> tuple[dict, Path]:
        initialize_workspace(ROOT, self.workspace, [self.project])
        request = plan_python(self.script, self.project)
        request_path = self.workspace / "requests" / "probe.json"
        write_json(request_path, request)
        return request, request_path

    def test_default_template_cannot_launch_a_process(self) -> None:
        shutil.copytree(ROOT / "spec", self.workspace / "spec")
        request_path = self.base / "request.json"
        write_json(request_path, plan_python(self.script, self.project))
        with patch("cbmd_harness.runner.subprocess.Popen") as process:
            with self.assertRaises(Refusal) as caught:
                execute(self.workspace, request_path)
        self.assertEqual(caught.exception.code, "CBMD_EXECUTION_ROOT_REFUSED")
        process.assert_not_called()
        self.assertFalse((self.workspace / "runtime" / "operations").exists())

    def test_initializer_binds_explicit_roots_without_inherited_authority(self) -> None:
        result = initialize_workspace(ROOT, self.workspace, [self.project])
        authority = load_json(self.workspace / "spec" / "CBMD-AUTHORITY.json")
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(authority["allowed_execution_roots"], [str(self.project.resolve())])
        self.assertEqual(authority["authority_id"], "CBMD.LOCAL.OPERATOR")
        self.assertEqual(authority["authority_effect"], "NONE")
        self.assertNotIn("PRIVATE_REPOSITORY_PUSH", authority["allowed_effects"])

    def test_initializer_refuses_nonempty_destination(self) -> None:
        self.configured()
        with self.assertRaises(Refusal):
            initialize_workspace(ROOT, self.workspace, [self.project])

    def test_initializer_refuses_filesystem_root(self) -> None:
        with self.assertRaises(Refusal):
            initialize_workspace(ROOT, self.workspace, [Path(self.project.anchor)])
        self.assertFalse(self.workspace.exists())

    def test_input_drift_refuses_before_intent(self) -> None:
        _, request_path = self.configured()
        self.script.write_text("print('changed')\n", encoding="utf-8")
        with patch("cbmd_harness.runner.subprocess.Popen") as process:
            with self.assertRaises(Refusal) as caught:
                execute(self.workspace, request_path)
        self.assertEqual(caught.exception.code, "CBMD_INPUT_DRIFT")
        process.assert_not_called()

    def test_sibling_directory_is_not_inside_execution_root(self) -> None:
        request, request_path = self.configured()
        sibling = self.base / "project-unapproved"
        sibling.mkdir()
        request["cwd"] = str(sibling)
        write_json(request_path, request)
        with self.assertRaises(Refusal) as caught:
            execute(self.workspace, request_path)
        self.assertEqual(caught.exception.code, "CBMD_EXECUTION_ROOT_REFUSED")

    def test_launch_error_preserves_one_failed_terminal(self) -> None:
        request, request_path = self.configured()
        with patch("cbmd_harness.runner.subprocess.Popen", side_effect=PermissionError(13, "launch denied")):
            terminal = execute(self.workspace, request_path)
        self.assertEqual(terminal["status"], "FAIL")
        self.assertEqual(terminal["launch_error"]["errno"], 13)
        self.assertEqual(verify_all(self.workspace)["status"], "PASS")
        self.assertEqual(execute(self.workspace, request_path)["terminal_root"], terminal["terminal_root"])
        intent = load_json(self.workspace / "runtime" / "operations" / request["operation_id"] / "INTENT.json")
        self.assertEqual(set(intent["governing_contract_roots"]),
                         {"authority_root", "lattice_root", "realization_space_root"})

    def test_missing_terminal_refuses_reexecution(self) -> None:
        request, request_path = self.configured()
        operation = self.workspace / "runtime" / "operations" / request["operation_id"]
        intent_body = {"schema": "cbmd.execution-intent.v1", "operation_id": request["operation_id"],
                       "request_root": root(request), "claim_boundary": "TEST_ONLY"}
        intent = {**intent_body, "intent_root": root(intent_body)}
        write_json(operation / "INTENT.json", intent)
        Ledger(self.workspace / "runtime" / "ledger").append("EXECUTION_INTENT", request["operation_id"], intent["intent_root"])
        with patch("cbmd_harness.runner.subprocess.Popen") as process:
            with self.assertRaises(Refusal) as caught:
                execute(self.workspace, request_path)
        self.assertEqual(caught.exception.code, "CBMD_OPERATION_UNCERTAIN")
        process.assert_not_called()
        self.assertEqual(verify_all(self.workspace)["status"], "DEGRADED")

    def test_timeout_preserves_terminal(self) -> None:
        _, request_path = self.configured()
        process = unittest.mock.Mock()
        process.wait.side_effect = [subprocess.TimeoutExpired(["probe"], 1), -9]
        with patch("cbmd_harness.runner.subprocess.Popen", return_value=process):
            terminal = execute(self.workspace, request_path)
        process.kill.assert_called_once()
        self.assertEqual(terminal["status"], "FAIL")
        self.assertTrue(terminal["timed_out"])
        self.assertEqual(verify_all(self.workspace)["status"], "PASS")

    def test_cached_terminal_does_not_hide_stream_tampering(self) -> None:
        request, request_path = self.configured()
        execute(self.workspace, request_path)
        (self.workspace / "runtime" / "operations" / request["operation_id"] / "stdout.bin").write_bytes(b"tampered")
        with self.assertRaises(Refusal) as caught:
            execute(self.workspace, request_path)
        self.assertEqual(caught.exception.code, "CBMD_STDOUT_ROOT_REFUSED")

    def test_clean_health_does_not_inherit_producer_evidence(self) -> None:
        initialize_workspace(ROOT, self.workspace, [self.project])
        result = health(self.workspace)
        self.assertEqual(result["dimensions"]["SOURCE_CORRESPONDENCE"], "GAP")
        for name in ("ADVERSE_COVERAGE", "TERMINAL_CUSTODY", "INTENT_BEFORE_EXECUTION", "STDOUT_STDERR_EXIT_CAPTURED"):
            self.assertEqual(result["dimensions"][name], "UNOBSERVED")

    def test_ucm_native_proof_remains_unbound(self) -> None:
        request = {"question_id": "Q", "claim_ids": ["C"], "requested_ceiling": "OBSERVED",
                   "method": "UCM_NATIVE_PROOF", "terminal_status": "PASS",
                   "lean_escape_status": "NOT_REQUIRED", "source_correspondence_status": "NOT_REQUIRED",
                   "adverse_status": "NOT_REQUIRED", "cold_replay_status": "NOT_REQUIRED",
                   "repo_qualification_status": "NOT_REQUIRED", "evidence_roots": ["1" * 64]}
        with self.assertRaises(Refusal) as caught:
            decide_promotion(request)
        self.assertEqual(caught.exception.code, "CBMD_UCM_ADAPTER_UNBOUND")

    def test_declared_outputs_are_required(self) -> None:
        request, request_path = self.configured()
        request["outputs"] = [{"path": "absent.json", "required": True, "role": "RESULT"}]
        write_json(request_path, request)
        terminal = execute(self.workspace, request_path)
        self.assertEqual(terminal["status"], "FAIL")
        self.assertFalse(terminal["outputs"][0]["present"])

    def test_deleted_operation_cannot_disappear_from_verification(self) -> None:
        request, request_path = self.configured()
        execute(self.workspace, request_path)
        shutil.rmtree(self.workspace / "runtime" / "operations" / request["operation_id"])
        with self.assertRaises(Refusal) as caught:
            verify_all(self.workspace)
        self.assertEqual(caught.exception.code, "CBMD_LEDGER_OPERATION_MISSING")

    def test_self_consistent_terminal_must_match_ledger_root(self) -> None:
        request, request_path = self.configured()
        execute(self.workspace, request_path)
        path = self.workspace / "runtime" / "operations" / request["operation_id"] / "TERMINAL.json"
        terminal = load_json(path)
        terminal["known_remainder"].append("changed after custody")
        body = {key: value for key, value in terminal.items() if key not in {"terminal_root", "host_observation"}}
        terminal["terminal_root"] = root(body)
        write_json(path, terminal)
        with self.assertRaises(Refusal) as caught:
            verify_all(self.workspace)
        self.assertEqual(caught.exception.code, "CBMD_LEDGER_TERMINAL_BINDING_REFUSED")


if __name__ == "__main__":
    unittest.main()
