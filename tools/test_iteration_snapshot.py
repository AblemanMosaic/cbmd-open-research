"""Adversarial snapshot-custody checks using isolated copies of real inputs."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest


SOURCE_ROOT = Path(__file__).resolve().parent.parent


class SnapshotCustodyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        specification = importlib.util.spec_from_file_location(
            "snapshot_verifier_under_test", SOURCE_ROOT / "tools/verify_iteration_snapshot.py"
        )
        if specification is None or specification.loader is None:
            raise RuntimeError("snapshot verifier cannot be imported")
        cls.verifier = importlib.util.module_from_spec(specification)
        specification.loader.exec_module(cls.verifier)

    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="cbmd-snapshot-adverse-")
        self.addCleanup(temporary.cleanup)
        self.fixture = Path(temporary.name).resolve()
        self.manifest = json.loads(
            (SOURCE_ROOT / self.verifier.SNAPSHOT).read_text(encoding="utf-8")
        )
        registry = json.loads((SOURCE_ROOT / "DISCOVERIES.json").read_text(encoding="utf-8"))
        discoveries = {row["id"]: row for row in registry["discoveries"]}

        self.copy_input(self.verifier.SNAPSHOT)
        self.copy_input("DISCOVERIES.json")
        for artifact in self.manifest["artifacts"]:
            self.copy_input(artifact["path"])
        self.claim_paths = []
        for binding in self.manifest["discovery_bindings"]:
            relative = discoveries[binding["discovery_id"]]["path"] + "/CLAIM.json"
            self.copy_input(relative)
            self.claim_paths.append(relative)

        original_root = self.verifier.ROOT
        self.addCleanup(setattr, self.verifier, "ROOT", original_root)
        self.verifier.ROOT = self.fixture

    def copy_input(self, relative: str) -> None:
        source = (SOURCE_ROOT / relative).resolve()
        destination = (self.fixture / relative).resolve()
        self.assertIn(SOURCE_ROOT, source.parents)
        self.assertIn(self.fixture, destination.parents)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)

    def write_manifest(self) -> None:
        (self.fixture / self.verifier.SNAPSHOT).write_text(
            json.dumps(self.manifest, indent=2) + "\n", encoding="utf-8"
        )

    def test_untouched_snapshot_passes_with_custody_only_scope(self) -> None:
        result = self.verifier.verify()
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["artifacts_checked"], len(self.manifest["artifacts"]))
        self.assertEqual(
            result["discovery_bindings_checked"], len(self.manifest["discovery_bindings"])
        )
        self.assertEqual(result["scope"], "RECORD_CUSTODY_AND_BINDINGS_ONLY")
        for nonclaim in ("lean_recompiled", "source_ledger_reconstructed", "independent_verification"):
            self.assertIs(result[nonclaim], False)

    def test_single_space_artifact_tamper_is_refused(self) -> None:
        artifact = self.fixture / self.manifest["artifacts"][0]["path"]
        original = artifact.read_bytes()
        artifact.write_bytes(original + b" ")
        self.assertEqual(json.loads(artifact.read_bytes()), json.loads(original))
        with self.assertRaisesRegex(ValueError, "snapshot digest mismatch"):
            self.verifier.verify()

    def test_discovery_claim_binding_tamper_is_refused(self) -> None:
        claim_path = self.fixture / self.claim_paths[0]
        claim = json.loads(claim_path.read_text(encoding="utf-8"))
        self.assertTrue(claim["ledger_binding"]["claim_ids"])
        claim["ledger_binding"]["claim_ids"][0] += ":tampered"
        claim_path.write_text(json.dumps(claim, indent=2) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "discovery and snapshot claims differ"):
            self.verifier.verify()

    def test_parent_traversal_artifact_path_is_refused(self) -> None:
        self.manifest["artifacts"][0]["path"] = "../outside.json"
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "unsafe repository path"):
            self.verifier.verify()

    def test_custody_manifest_cannot_claim_completed_proof_replay(self) -> None:
        self.manifest["full_proof_replay_from_this_checkout"] = "PASS"
        self.write_manifest()
        with self.assertRaisesRegex(ValueError, "custody checker cannot certify proof replay"):
            self.verifier.verify()


if __name__ == "__main__":
    unittest.main(verbosity=2)
