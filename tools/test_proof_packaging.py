"""Adversarial source-envelope tests; no compiler or network is required."""
from __future__ import annotations

import hashlib
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest


SOURCE_ROOT = Path(__file__).resolve().parent.parent


class ProofPackagingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        specification = importlib.util.spec_from_file_location(
            "proof_source_verifier_under_test", SOURCE_ROOT / "tools/verify_proof_sources.py"
        )
        if specification is None or specification.loader is None:
            raise RuntimeError("proof source verifier cannot be imported")
        cls.verifier = importlib.util.module_from_spec(specification)
        specification.loader.exec_module(cls.verifier)

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="cbmd-proof-envelope-adverse-")
        self.addCleanup(temporary.cleanup)
        self.fixture = Path(temporary.name).resolve()
        previous_root = self.verifier.ROOT
        self.addCleanup(setattr, self.verifier, "ROOT", previous_root)
        self.verifier.ROOT = self.fixture
        self.manifest = {
            "schema": "cbmd.proof-source-manifest.v1",
            "project_path": "proofs/native", "source_library_root": "proofs/native/lean",
            "toolchain": self.verifier.TOOLCHAIN,
            "mathlib_revision": self.verifier.MATHLIB_REVISION,
            "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
            "targets": ["OAI.Target"], "files": [],
        }
        self.put("proofs/native/lean-toolchain", self.verifier.TOOLCHAIN + "\n")
        self.put("proofs/native/lakefile.lean",
                 'import Lake\npackage cbmd where\n  fixedToolchain := true\n'
                 'require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @\n'
                 '  "' + self.verifier.MATHLIB_REVISION + '"\n')
        self.put("proofs/native/lake-manifest.json", json.dumps({
            "fixedToolchain": True, "packages": [{
                "name": "mathlib", "type": "git", "rev": self.verifier.MATHLIB_REVISION,
                "url": "https://github.com/leanprover-community/mathlib4.git",
            }],
        }))
        self.put("proofs/native/LICENSES/UPSTREAM.txt", "Retained fixture license.\n")
        self.put("tools/replay_lean.py", "# Synthetic runner input.\n")
        self.put("tools/verify_proof_sources.py", "# Synthetic verifier input.\n")
        self.put("proofs/native/lean/OAI/Base.lean", "import Mathlib\ntheorem base : True := by trivial\n")
        self.put("proofs/native/lean/OAI/Target.lean",
                 "import OAI.Base\n/- nested /- sorry -/ axiom admit -/\n"
                 '-- unsafe native_decide\ndef description := "sorry and axiom"\n'
                 "theorem target : True := base\n")
        self.save_manifest()

    def put(self, relative: str, content: str, declared: bool = True) -> None:
        path = self.fixture / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = content.encode("utf-8")
        path.write_bytes(payload)
        if declared:
            self.manifest["files"] = [row for row in self.manifest["files"] if row["path"] != relative]
            self.manifest["files"].append({
                "path": relative, "sha256": hashlib.sha256(payload).hexdigest(),
                "bytes": len(payload), "origin": "ADVERSARIAL_TEST_FIXTURE",
            })

    def save_manifest(self) -> None:
        (self.fixture / self.verifier.MANIFEST).write_text(
            json.dumps(self.manifest, indent=2) + "\n", encoding="utf-8"
        )

    def test_complete_fixture_passes_without_claiming_compilation(self) -> None:
        result = self.verifier.verify()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["target_import_closure_modules"], 2)
        self.assertEqual(result["scope"], "SOURCE_CUSTODY_AND_NO_ESCAPE_ONLY")
        for nonclaim in ("lean_recompiled", "actual_axiom_dependencies_checked",
                         "independent_verification"):
            self.assertIs(result[nonclaim], False)

    def test_same_size_source_tamper_is_refused(self) -> None:
        path = self.fixture / "proofs/native/lean/OAI/Base.lean"
        original = path.read_bytes()
        path.write_bytes(original.replace(b"base", b"fake"))
        self.assertEqual(len(original), len(path.read_bytes()))
        with self.assertRaisesRegex(ValueError, "digest mismatch"):
            self.verifier.verify()

    def test_missing_transitive_import_is_refused_even_when_manifest_is_rehashed(self) -> None:
        self.put("proofs/native/lean/OAI/Base.lean",
                 "import OAI.Missing\ntheorem base : True := by trivial\n")
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "missing local import: OAI.Missing"):
            self.verifier.verify()

    def test_multiline_import_cannot_hide_a_missing_module(self) -> None:
        self.put("proofs/native/lean/OAI/Target.lean", "import\n OAI.Base\n OAI.Hidden\n")
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "missing local import: OAI.Hidden"):
            self.verifier.verify()

    def test_rehashed_proof_escape_in_import_is_refused(self) -> None:
        for escape in ("sorry", "admit", "axiom", "unsafe", "native_decide", "sorryAx",
                       "Lean.sorryAx"):
            with self.subTest(escape=escape):
                self.put("proofs/native/lean/OAI/Base.lean", "import Mathlib\n" + escape + "\n")
                self.save_manifest()
                with self.assertRaisesRegex(ValueError, "Lean proof escape"):
                    self.verifier.verify()

    def test_disabled_kernel_check_is_refused(self) -> None:
        self.put("proofs/native/lean/OAI/Base.lean", "import Mathlib\nset_option debug.skipKernelTC true\n")
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "kernel check disabled"):
            self.verifier.verify()

    def test_unbound_extra_lean_source_is_refused(self) -> None:
        self.put("proofs/native/lean/OAI/Hidden.lean", "axiom bad : False\n", declared=False)
        with self.assertRaisesRegex(ValueError, "unbound Lean source"):
            self.verifier.verify()

    def test_parent_traversal_is_refused(self) -> None:
        self.manifest["files"][0]["path"] = "../escape.txt"
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "unsafe repository path"):
            self.verifier.verify()

    def test_duplicate_input_is_refused(self) -> None:
        self.manifest["files"].append(dict(self.manifest["files"][0]))
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "duplicate proof input"):
            self.verifier.verify()

    def test_unbound_runner_is_refused(self) -> None:
        self.manifest["files"] = [row for row in self.manifest["files"]
                                  if row["path"] != "tools/replay_lean.py"]
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "runner or pinned project input"):
            self.verifier.verify()

    def test_dependency_revision_drift_is_refused(self) -> None:
        path = "proofs/native/lake-manifest.json"
        dependencies = json.loads((self.fixture / path).read_text(encoding="utf-8"))
        dependencies["packages"][0]["rev"] = "0" * 40
        self.put(path, json.dumps(dependencies))
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "mathlib binding mismatch"):
            self.verifier.verify()

    def test_new_axiom_cannot_be_added_to_the_allowlist(self) -> None:
        self.manifest["allowed_axioms"].append("sorryAx")
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "unapproved axiom allowlist"):
            self.verifier.verify()

    def test_optional_import_inventory_cannot_disagree(self) -> None:
        self.manifest["source_imports"] = {"OAI.Target": ["OAI.Base"]}
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "declared source imports differ"):
            self.verifier.verify()

    def test_local_import_cycle_is_refused(self) -> None:
        self.put("proofs/native/lean/OAI/Base.lean", "import OAI.Target\n")
        self.save_manifest()
        with self.assertRaisesRegex(ValueError, "cyclic local imports"):
            self.verifier.verify()


if __name__ == "__main__":
    unittest.main(verbosity=2)
