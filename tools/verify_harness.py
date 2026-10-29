"""Qualify the portable CBMD harness from a clean checkout using stdlib only."""
from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HARNESS = ROOT / "software" / "harness"
sys.path.insert(0, str(HARNESS))

from cbmd_harness.canonical import file_sha256, load_json  # noqa: E402
from cbmd_harness.courts import court  # noqa: E402


def main() -> int:
    manifest = load_json(HARNESS / "provenance" / "PORTABLE_FILES.json")
    seen = set()
    for item in manifest["files"]:
        relative = Path(item["path"])
        path = (HARNESS / relative).resolve()
        if relative.is_absolute() or ".." in relative.parts or item["path"] in seen or not path.is_relative_to(HARNESS.resolve()):
            print(json.dumps({"status": "FAIL", "reason": "PORTABLE_MANIFEST_PATH_REFUSED", "path": item["path"]}))
            return 1
        seen.add(item["path"])
        if not path.is_file() or file_sha256(path) != item["sha256"]:
            print(json.dumps({"status": "FAIL", "reason": "PORTABLE_SOURCE_DRIFT", "path": item["path"]}))
            return 1
    contract = load_json(HARNESS / "provenance" / "TEST_CONTRACT.json")
    suite = unittest.defaultTestLoader.discover(str(HARNESS / "tests"), top_level_dir=str(HARNESS))
    def identities(item):
        if isinstance(item, unittest.TestSuite):
            return [identity for child in item for identity in identities(child)]
        return [item.id()]
    discovered = sorted(identities(suite))
    if discovered != contract["required_identities"] or len(discovered) != contract["required_test_count"]:
        print(json.dumps({"status": "FAIL", "reason": "REQUIRED_TEST_INVENTORY_MISMATCH"}))
        return 1
    result = court(HARNESS)
    result["source_files_verified"] = len(manifest["files"])
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0 if result["status"] == "PASS" and result["skips"] == 0 and result["tests_run"] > 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
