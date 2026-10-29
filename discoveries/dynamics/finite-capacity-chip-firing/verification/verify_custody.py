"""Verify the sanitized public projection against its source-custody manifest."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


DISCOVERY = Path(__file__).resolve().parent.parent
MANIFEST = DISCOVERY / "evidence" / "SOURCE_CUSTODY.json"
RECEIPT = DISCOVERY / "evidence" / "SOURCE_BINDING_RECEIPT.json"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(value: str) -> Path:
    pure = PurePosixPath(value)
    if pure.is_absolute() or not pure.parts or any(part in ("", ".", "..") for part in pure.parts):
        raise ValueError(f"unsafe custody path: {value!r}")
    return Path(*pure.parts)


def main() -> int:
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
    expected = manifest["source_repository"]
    if receipt["source_binding"] != expected:
        raise ValueError("source binding and custody manifest differ")
    checked: list[str] = []
    for member in manifest["members"]:
        public = DISCOVERY / relative(member["public_copy"])
        if not public.is_file():
            raise ValueError(f"missing public source copy: {member['public_copy']}")
        actual = digest(public)
        if actual != member["sha256"]:
            raise ValueError(f"public source hash drift: {member['public_copy']}")
        checked.append(member["public_copy"])
    forbidden = re.compile(r"(?i)([a-z]:\\users\\|/home/[^/]+/|\\\.codex\\)")
    for path in DISCOVERY.rglob("*"):
        if path.resolve() == Path(__file__).resolve():
            continue
        if path.is_file() and path.suffix.lower() in {".md", ".json", ".py", ".lean", ".toml"}:
            text = path.read_text(encoding="utf-8")
            if forbidden.search(text):
                raise ValueError(f"personal machine path in public artifact: {path.relative_to(DISCOVERY)}")
    result = {
        "schema": "cbmd.finite_dynamics.public_custody_check.v1",
        "status": "PASS",
        "checked_members": len(checked),
        "source_commit": expected["commit"],
        "qualification_run": expected["qualification_run"],
        "authority_effect": "NONE",
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc)}, sort_keys=True), file=sys.stderr)
        raise SystemExit(1)
