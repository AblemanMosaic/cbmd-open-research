"""Deterministically assemble the standalone low-sector pairing explorer."""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
TEMPLATE = HERE / "template.html"
CORE = HERE / "low_sector_pairing_core.js"
DEFAULT_OUTPUT = ROOT / "GENUS_TWO_LOW_SECTOR_PAIRING_EXPLORER.html"
PLACEHOLDER = "/*__CORE__*/"


def render() -> str:
    template = TEMPLATE.read_text(encoding="utf-8")
    core = CORE.read_text(encoding="utf-8")
    if template.count(PLACEHOLDER) != 1:
        raise RuntimeError("template must contain exactly one core placeholder")
    document = template.replace(PLACEHOLDER, core)
    for marker in ("<!doctype html>", "default-src 'none'", '<html lang="en">', "</html>"):
        if marker not in document:
            raise RuntimeError(f"assembled document is missing {marker!r}")
    if re.search(r'<(?:script|link|img|iframe|audio|video|source)\b[^>]*(?:src|href)=["\']https?://', document, re.I):
        raise RuntimeError("assembled document contains an external resource URL")
    return document.rstrip() + "\n"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="compare with the delivered output without writing")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    output = args.output.resolve()
    data = render().encode("utf-8")
    if args.check:
        if output.is_symlink() or not output.is_file():
            raise SystemExit(f"BUILD_CHECK_REFUSED: missing regular output: {output}")
        actual = output.read_bytes()
        if actual != data:
            raise SystemExit("BUILD_CHECK_FAILED: " + json.dumps({"expected_sha256": digest(data), "actual_sha256": digest(actual)}))
        status = "PASS"
    else:
        if output.is_symlink():
            raise SystemExit(f"BUILD_REFUSED: output is a symbolic link: {output}")
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(data)
        status = "BUILT"
    print(json.dumps({"status": status, "output": output.name, "bytes": len(data), "sha256": digest(data)}, sort_keys=True))


if __name__ == "__main__":
    main()
