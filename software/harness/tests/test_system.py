from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from cbmd_harness.adapters import plan_lean
from cbmd_harness.canonical import CanonicalError, canonical_bytes, file_sha256, root, write_json
from cbmd_harness.contracts import load_and_verify_specs
from cbmd_harness.courts import lean_escape_scan
from cbmd_harness.evidence import health, verify_all
from cbmd_harness.ledger import Ledger
from cbmd_harness.refusals import Refusal
from cbmd_harness.runner import execute
from cbmd_harness.promotion import decide_promotion
from cbmd_harness.state import refresh_state
from cbmd_harness.recovery import recover_uncertain
from cbmd_harness.contracts import verify_lattice


ROOT = Path(__file__).resolve().parent.parent


class CanonicalTests(unittest.TestCase):
    def test_key_order_is_stable(self) -> None:
        self.assertEqual(canonical_bytes({"b": 1, "a": 2}), b'{"a":2,"b":1}')

    def test_float_refuses(self) -> None:
        with self.assertRaises(CanonicalError):
            canonical_bytes({"x": 1.0})


class ContractTests(unittest.TestCase):
    def test_specs_validate_and_root(self) -> None:
        roots = load_and_verify_specs(ROOT)
        self.assertEqual(set(roots), {"authority_root", "lattice_root", "realization_space_root"})
        self.assertTrue(all(len(value) == 64 for value in roots.values()))

    def test_dangling_lattice_edge_refuses(self) -> None:
        lattice = json.loads((ROOT / "spec" / "CBMD-CAPABILITY-LATTICE.json").read_text(encoding="utf-8"))
        lattice["edges"].append({"from":"CBMD.ORIENT","to":"CBMD.MISSING","relation":"PRECEDES"})
        with self.assertRaises(Refusal):
            verify_lattice(lattice)


class LedgerTests(unittest.TestCase):
    def test_append_and_verify(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            ledger = Ledger(Path(temporary))
            first = ledger.append("INTENT", "OP-1", "1" * 64)
            second = ledger.append("TERMINAL", "OP-1", "2" * 64)
            state = ledger.verify()
            self.assertEqual(state["count"], 2)
            self.assertEqual(state["head"], second["event_root"])
            self.assertEqual(first["previous"], "0" * 64)

    def test_tamper_refuses(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            ledger = Ledger(Path(temporary))
            ledger.append("INTENT", "OP-1", "1" * 64)
            ledger.journal.write_text(ledger.journal.read_text(encoding="utf-8").replace("INTENT", "OTHER"), encoding="utf-8")
            with self.assertRaises(Refusal):
                ledger.verify()

    def test_append_once_is_idempotent_and_conflict_sensitive(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            ledger = Ledger(Path(temporary))
            first = ledger.append_once("STATE", "CYCLE-1", "1" * 64)
            second = ledger.append_once("STATE", "CYCLE-1", "1" * 64)
            self.assertEqual(first, second)
            self.assertEqual(ledger.verify()["count"], 1)
            with self.assertRaises(Refusal):
                ledger.append_once("STATE", "CYCLE-1", "2" * 64)


class LeanCourtTests(unittest.TestCase):
    def test_comments_do_not_trigger_but_sorry_does(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            path = Path(temporary) / "Proof.lean"
            path.write_text("-- sorry\ntheorem x : True := by\n  sorry\n", encoding="utf-8")
            result = lean_escape_scan([path])
            self.assertEqual(result["status"], "FAIL")
            self.assertEqual(len(result["findings"]), 1)

    def test_nested_block_comments_are_ignored(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            path = Path(temporary) / "Proof.lean"
            path.write_text("/- sorry /- axiom -/ admit -/\ntheorem x : True := by trivial\n", encoding="utf-8")
            self.assertEqual(lean_escape_scan([path])["status"], "PASS")


class LeanAdapterTests(unittest.TestCase):
    def test_plan_pins_minimal_path_provenance_and_package_safe_directories(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            root_path = Path(temporary)
            project = root_path / "project"
            module = project / "lean" / "Example" / "Proof.lean"
            package_b = project / ".lake" / "packages" / "beta"
            package_a = project / ".lake" / "packages" / "alpha"
            provenance = project / "provenance" / "LEAN_SOURCE_BOUNDARY.json"
            for path in (module.parent, package_b / ".git", package_a / ".git", provenance.parent):
                path.mkdir(parents=True, exist_ok=True)
            (project / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n", encoding="utf-8")
            (project / "lakefile.lean").write_text("package Example\n", encoding="utf-8")
            (project / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
            module.write_text("theorem example : True := by trivial\n", encoding="utf-8")
            dependency = project / "lean" / "Example" / "Dependency.lean"
            transitive = project / "lean" / "Example" / "Transitive.lean"
            dependency.write_text("import Example.Transitive\ntheorem dependency : True := by trivial\n", encoding="utf-8")
            transitive.write_text("theorem transitive : True := by trivial\n", encoding="utf-8")
            module.write_text("import Example.Dependency\ntheorem example : True := by trivial\n", encoding="utf-8")
            provenance.write_text("{}\n", encoding="utf-8")
            lake = root_path / "toolchain" / "lake.exe"
            git = root_path / "git" / "git.exe"
            lake.parent.mkdir()
            git.parent.mkdir()
            lake.write_bytes(b"lake")
            git.write_bytes(b"git")

            with patch("cbmd_harness.adapters._find_lake", return_value=lake.resolve()), patch(
                "cbmd_harness.adapters._find_git", return_value=git.resolve()
            ):
                request = plan_lean(project, "Example.Proof", question_id="Q", claim_ids=["C"])
                before = request["operation_id"]
                (project / ".lake" / "packages" / "gamma" / ".git").mkdir(parents=True)
                after = plan_lean(project, "Example.Proof", question_id="Q", claim_ids=["C"])

            environment = request["environment_delta"]
            self.assertEqual(environment["PATH"], str(lake.parent) + __import__('os').pathsep + str(git.parent))
            self.assertEqual(environment["GIT_CONFIG_COUNT"], "2")
            self.assertEqual(environment["GIT_CONFIG_KEY_0"], "safe.directory")
            self.assertEqual(environment["GIT_CONFIG_KEY_1"], "safe.directory")
            self.assertEqual(
                [environment["GIT_CONFIG_VALUE_0"], environment["GIT_CONFIG_VALUE_1"]],
                sorted([str(package_a.resolve()), str(package_b.resolve())]),
            )
            self.assertIn(str(provenance), [item["path"] for item in request["inputs"]])
            local_imports = [item["path"] for item in request["inputs"] if item["role"] == "LOCAL_IMPORT"]
            self.assertEqual(local_imports, sorted([str(dependency.resolve()), str(transitive.resolve())]))
            self.assertNotEqual(before, after["operation_id"])


class RunnerTests(unittest.TestCase):
    def _workspace(self, temporary: str) -> Path:
        workspace = Path(temporary) / "harness"
        (workspace / "spec").mkdir(parents=True)
        for name in ("CBMD-AUTHORITY.json", "CBMD-CAPABILITY-LATTICE.json", "CBMD-REALIZATION-SPACE-CONTRACT.json"):
            (workspace / "spec" / name).write_bytes((ROOT / "spec" / name).read_bytes())
        authority_path = workspace / "spec" / "CBMD-AUTHORITY.json"
        authority = json.loads(authority_path.read_text(encoding="utf-8"))
        authority["allowed_execution_roots"] = [temporary.replace("\\", "/")]
        write_json(authority_path, authority)
        return workspace

    def test_exact_run_and_idempotent_return(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            workspace = self._workspace(temporary)
            script = Path(temporary) / "probe.py"
            script.write_text("import sys\nprint('OUT')\nprint('ERR', file=sys.stderr)\n", encoding="utf-8")
            request = {
                "schema":"cbmd.run-request.v1","operation_id":"TEST-OP-1","question_id":"Q","claim_ids":[],
                "runner_id":"TEST","argv":[__import__('sys').executable,str(script)],"cwd":temporary,
                "environment_delta":{},"timeout_seconds":30,"expected_exit_codes":[0],
                "inputs":[{"path":str(script),"sha256":file_sha256(script),"role":"SCRIPT"}],"outputs":[],
                "claim_boundary":"TEST_ONLY","known_remainder":[],
                "authority_id":"CBMD.LOCAL.OPERATOR"
            }
            request_path = Path(temporary) / "request.json"
            write_json(request_path, request)
            first = execute(workspace, request_path)
            second = execute(workspace, request_path)
            self.assertEqual(first["terminal_root"], second["terminal_root"])
            self.assertEqual(first["status"], "PASS")
            self.assertEqual(verify_all(workspace)["status"], "PASS")

    def test_changed_request_same_operation_refuses(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            workspace = self._workspace(temporary)
            script = Path(temporary) / "probe.py"
            script.write_text("print('A')\n", encoding="utf-8")
            request = {
                "schema":"cbmd.run-request.v1","operation_id":"TEST-OP-2","question_id":"Q","claim_ids":[],
                "runner_id":"TEST","argv":[__import__('sys').executable,str(script)],"cwd":temporary,
                "environment_delta":{},"timeout_seconds":30,"expected_exit_codes":[0],
                "inputs":[{"path":str(script),"sha256":file_sha256(script),"role":"SCRIPT"}],"outputs":[],
                "claim_boundary":"TEST_ONLY","known_remainder":[],
                "authority_id":"CBMD.LOCAL.OPERATOR"
            }
            request_path = Path(temporary) / "request.json"
            write_json(request_path, request)
            execute(workspace, request_path)
            request["question_id"] = "CHANGED"
            write_json(request_path, request)
            with self.assertRaises(Refusal):
                execute(workspace, request_path)

    def test_keyboard_interrupt_writes_aborted_terminal(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            workspace = self._workspace(temporary)
            script = Path(temporary) / "probe.py"
            script.write_text("print('unreached')\n", encoding="utf-8")
            request = {
                "schema":"cbmd.run-request.v1","operation_id":"TEST-INTERRUPT","question_id":"Q",
                "claim_ids":[],"runner_id":"TEST","argv":[__import__('sys').executable,str(script)],
                "cwd":temporary,"environment_delta":{},"timeout_seconds":30,"expected_exit_codes":[0],
                "inputs":[{"path":str(script),"sha256":file_sha256(script),"role":"SCRIPT"}],
                "outputs":[],"claim_boundary":"TEST_ONLY","known_remainder":[],
                "authority_id":"CBMD.LOCAL.OPERATOR"
            }
            request_path = Path(temporary) / "request.json"
            write_json(request_path, request)

            class InterruptedProcess:
                def __init__(self) -> None:
                    self.killed = False

                def wait(self, timeout=None):
                    if timeout is not None:
                        raise KeyboardInterrupt
                    return -9

                def poll(self):
                    return None

                def kill(self) -> None:
                    self.killed = True

            process = InterruptedProcess()
            with patch("cbmd_harness.runner.subprocess.Popen", return_value=process):
                terminal = execute(workspace, request_path)

            self.assertTrue(process.killed)
            self.assertEqual(terminal["status"], "ABORTED")
            self.assertTrue(terminal["interrupted"])
            self.assertTrue((workspace / "runtime" / "operations" / "TEST-INTERRUPT" / "TERMINAL.json").is_file())
            self.assertEqual(verify_all(workspace)["status"], "PASS")

    def test_uncertain_recovery_is_unobserved_and_not_claim_eligible(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            workspace = self._workspace(temporary)
            operation_dir = workspace / "runtime" / "operations" / "TEST-UNCERTAIN"
            operation_dir.mkdir(parents=True)
            intent_body = {
                "schema":"cbmd.execution-intent.v1","operation_id":"TEST-UNCERTAIN",
                "request_root":"1" * 64,"runner_id":"TEST","executable":{},"argv":["probe"],
                "cwd_identity":"2" * 64,"environment_delta":{},"inputs":[],
                "authority_id":"CBMD.LOCAL.OPERATOR",
                "claim_boundary":"TEST_ONLY"
            }
            write_json(operation_dir / "INTENT.json", {**intent_body, "intent_root":root(intent_body)})
            Ledger(workspace / "runtime" / "ledger").append("EXECUTION_INTENT", "TEST-UNCERTAIN", root(intent_body))
            (operation_dir / "stdout.bin").write_bytes(b"partial")
            (operation_dir / "stderr.bin").write_bytes(b"")
            terminal = recover_uncertain(
                workspace,
                "TEST-UNCERTAIN",
                "OWNED_PROCESS_NOT_OBSERVED_AFTER_CONTROLLED_INTERRUPT",
            )
            self.assertEqual(terminal["status"], "UNOBSERVED")
            self.assertFalse(terminal["recovery"]["claim_eligible"])
            self.assertEqual(verify_all(workspace)["status"], "PASS")

    def test_controller_disappearance_recovery_is_unobserved(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            workspace = self._workspace(temporary)
            operation_dir = workspace / "runtime" / "operations" / "TEST-CONTROLLER-GONE"
            operation_dir.mkdir(parents=True)
            intent_body = {
                "schema":"cbmd.execution-intent.v1","operation_id":"TEST-CONTROLLER-GONE",
                "request_root":"3" * 64,"runner_id":"TEST","executable":{},"argv":["probe"],
                "cwd_identity":"4" * 64,"environment_delta":{},"inputs":[],
                "authority_id":"CBMD.LOCAL.OPERATOR",
                "claim_boundary":"TEST_ONLY"
            }
            write_json(operation_dir / "INTENT.json", {**intent_body, "intent_root":root(intent_body)})
            Ledger(workspace / "runtime" / "ledger").append("EXECUTION_INTENT", "TEST-CONTROLLER-GONE", root(intent_body))
            (operation_dir / "stdout.bin").write_bytes(b"")
            (operation_dir / "stderr.bin").write_bytes(b"")
            terminal = recover_uncertain(
                workspace,
                "TEST-CONTROLLER-GONE",
                "CONTROLLER_RETURNED_WITHOUT_TERMINAL_AND_NO_OWNED_PROCESS_OBSERVED",
            )
            self.assertEqual(terminal["status"], "UNOBSERVED")
            self.assertFalse(terminal["recovery"]["claim_eligible"])
            self.assertEqual(verify_all(workspace)["status"], "PASS")

    def test_secret_environment_refuses_before_intent(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            workspace = self._workspace(temporary)
            script = Path(temporary) / "probe.py"
            script.write_text("print('A')\n", encoding="utf-8")
            request = {
                "schema":"cbmd.run-request.v1","operation_id":"TEST-SECRET","question_id":"Q","claim_ids":[],
                "runner_id":"TEST","argv":[__import__('sys').executable,str(script)],"cwd":temporary,
                "environment_delta":{"API_TOKEN":"forbidden"},"timeout_seconds":30,"expected_exit_codes":[0],
                "inputs":[{"path":str(script),"sha256":file_sha256(script),"role":"SCRIPT"}],"outputs":[],
                "claim_boundary":"TEST_ONLY","known_remainder":[],
                "authority_id":"CBMD.LOCAL.OPERATOR"
            }
            request_path = Path(temporary) / "request.json"
            write_json(request_path, request)
            with self.assertRaises(Refusal):
                execute(workspace, request_path)
            self.assertFalse((workspace / "runtime" / "operations").exists())

    def test_stdout_tamper_is_detected(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            workspace = self._workspace(temporary)
            script = Path(temporary) / "probe.py"
            script.write_text("print('A')\n", encoding="utf-8")
            request = {
                "schema":"cbmd.run-request.v1","operation_id":"TEST-TAMPER","question_id":"Q","claim_ids":[],
                "runner_id":"TEST","argv":[__import__('sys').executable,str(script)],"cwd":temporary,
                "environment_delta":{},"timeout_seconds":30,"expected_exit_codes":[0],
                "inputs":[{"path":str(script),"sha256":file_sha256(script),"role":"SCRIPT"}],"outputs":[],
                "claim_boundary":"TEST_ONLY","known_remainder":[],
                "authority_id":"CBMD.LOCAL.OPERATOR"
            }
            request_path = Path(temporary) / "request.json"
            write_json(request_path, request)
            execute(workspace, request_path)
            (workspace / "runtime" / "operations" / "TEST-TAMPER" / "stdout.bin").write_bytes(b"changed")
            with self.assertRaises(Refusal):
                verify_all(workspace)


class PromotionTests(unittest.TestCase):
    def _request(self) -> dict:
        return {
            "question_id":"Q","claim_ids":["C"],"requested_ceiling":"COMPILED_PROOF","method":"LEAN_LAKE",
            "terminal_status":"PASS","lean_escape_status":"PASS","source_correspondence_status":"NOT_REQUIRED",
            "adverse_status":"PASS","cold_replay_status":"NOT_REQUIRED","repo_qualification_status":"NOT_REQUIRED",
            "evidence_roots":["1" * 64],
        }

    def test_compiled_proof_promotes(self) -> None:
        self.assertEqual(decide_promotion(self._request())["ceiling"], "COMPILED_PROOF")

    def test_escape_refuses_proof(self) -> None:
        request = self._request()
        request["lean_escape_status"] = "FAIL"
        with self.assertRaises(Refusal):
            decide_promotion(request)

    def test_finite_check_cannot_promote_to_general_proof(self) -> None:
        request = self._request()
        request["method"] = "PYTHON_EXACT"
        with self.assertRaises(Refusal):
            decide_promotion(request)


class StateTests(unittest.TestCase):
    def test_state_is_rooted_and_idempotent(self) -> None:
        with tempfile.TemporaryDirectory(dir=ROOT) as temporary:
            root_path = Path(temporary)
            candidate = {
                "cycle_id":"CYCLE-1","question_id":"Q","status":"ACTIVE","claim_ids":["C"],
                "evidence_roots":[],"substantive_advance":False,"consecutive_no_advance_cycles":0,
                "next_action":"compile","known_remainder":[],
            }
            first = refresh_state(root_path, candidate)
            second = refresh_state(root_path, candidate)
            self.assertEqual(first, second)
            self.assertEqual(len(first["state_root"]), 64)


class HealthTests(unittest.TestCase):
    def test_health_exposes_remainder(self) -> None:
        result = health(ROOT)
        self.assertEqual(result["status"], "DEGRADED")
        self.assertGreater(len(result["known_remainder"]), 0)
        self.assertIn("common_mode_limits", result)
        self.assertEqual(result["dimensions"]["ADVERSE_COVERAGE"], "UNOBSERVED")
        self.assertTrue(any("No qualified mathematical-adapter mutation receipt" in item for item in result["known_remainder"]))


if __name__ == "__main__":
    unittest.main()
