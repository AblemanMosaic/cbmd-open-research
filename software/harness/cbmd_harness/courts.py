from __future__ import annotations

import re
import unittest
from pathlib import Path
from typing import Any

from .evidence import verify_all


ESCAPE_TOKENS = re.compile(r"\b(sorry|admit|axiom)\b")


def _strip_lean_comments(text: str) -> str:
    output: list[str] = []
    index = 0
    depth = 0
    in_string = False
    while index < len(text):
        pair = text[index:index + 2]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
            continue
        if not in_string and pair == "/-":
            depth = 1
            index += 2
            continue
        if not in_string and pair == "--":
            newline = text.find("\n", index)
            index = len(text) if newline < 0 else newline
            continue
        char = text[index]
        if char == '"' and (index == 0 or text[index - 1] != "\\"):
            in_string = not in_string
            output.append(" ")
        elif in_string:
            output.append(" ")
        else:
            output.append(char)
        index += 1
    return "".join(output)


def lean_escape_scan(paths: list[Path]) -> dict[str, Any]:
    findings: list[dict[str, Any]] = []
    for path in paths:
        clean = _strip_lean_comments(path.read_text(encoding="utf-8"))
        for match in ESCAPE_TOKENS.finditer(clean):
            line = clean.count("\n", 0, match.start()) + 1
            findings.append({"path": str(path), "line": line, "token": match.group(1)})
    return {
        "schema": "cbmd.lean-escape-court.v1",
        "status": "PASS" if not findings else "FAIL",
        "findings": findings,
        "claim_boundary": "Token scan does not establish theorem-to-source correspondence.",
        "authority_effect": "NONE",
    }


def run_tests(root_path: Path) -> dict[str, Any]:
    suite = unittest.defaultTestLoader.discover(str(root_path / "tests"), pattern="test_*.py", top_level_dir=str(root_path))
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return {
        "schema": "cbmd.harness-court.v1",
        "status": "PASS" if result.wasSuccessful() and result.testsRun > 0 and not result.skipped else "FAIL",
        "tests_run": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "skips": len(result.skipped),
        "authority_effect": "NONE",
    }


def court(root_path: Path, test_root: Path | None = None) -> dict[str, Any]:
    evidence = verify_all(root_path)
    tests = run_tests(test_root or root_path)
    status = "PASS" if evidence["status"] == "PASS" and tests["status"] == "PASS" and tests["skips"] == 0 else "FAIL"
    return {
        "schema": "cbmd.combined-court.v1",
        "status": status,
        "evidence_status": evidence["status"],
        "test_status": tests["status"],
        "tests_run": tests["tests_run"],
        "failures": tests["failures"],
        "errors": tests["errors"],
        "skips": tests["skips"],
        "standing": "DETERMINISTIC_CONTROL_PASSED" if status == "PASS" else "UNQUALIFIED",
        "claim_boundary": "Instrument behavior only; no mathematical claim or independent verification follows.",
        "authority_effect": "NONE",
    }
