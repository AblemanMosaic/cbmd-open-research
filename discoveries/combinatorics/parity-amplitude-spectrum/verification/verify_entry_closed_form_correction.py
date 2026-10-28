from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


DISCOVERY = Path(__file__).resolve().parent.parent
RECEIPT = DISCOVERY / "evidence" / "ENTRY_CLOSED_FORM_CORRECTION_RECEIPT.json"


def strip_lean(text: str) -> str:
    out: list[str] = []
    i = depth = 0
    in_string = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-": depth += 1; i += 2; continue
            if pair == "-/": depth -= 1; i += 2; continue
            i += 1; continue
        if not in_string and pair == "/-": depth = 1; i += 2; continue
        if not in_string and pair == "--":
            newline = text.find("\n", i)
            i = len(text) if newline < 0 else newline
            continue
        char = text[i]
        if char == '"' and (i == 0 or text[i - 1] != "\\"):
            in_string = not in_string
        out.append(" " if in_string else char)
        i += 1
    return "".join(out)


receipt = json.loads(RECEIPT.read_text(encoding="utf-8"))
lean_path = DISCOVERY / receipt["lean_counterexample"]["path"]
audit_path = DISCOVERY / receipt["finite_audit"]["path"]
revised_path = DISCOVERY / receipt["revised_formula_lean"]["path"]
lean_hash = hashlib.sha256(lean_path.read_bytes()).hexdigest()
audit_hash = hashlib.sha256(audit_path.read_bytes()).hexdigest()
revised_hash = hashlib.sha256(revised_path.read_bytes()).hexdigest()
assert lean_hash == receipt["lean_counterexample"]["sha256"]
assert audit_hash == receipt["finite_audit"]["sha256"]
assert revised_hash == receipt["revised_formula_lean"]["sha256"]
assert receipt["lean_counterexample"]["status"] == "PASS"
assert receipt["disposition"] == "REFUTED_AS_STATED"
assert receipt["revised_formula_formal_status"] == "COMPILED_PROOF"
assert not re.search(r"\b(sorry|admit|axiom)\b", strip_lean(lean_path.read_text(encoding="utf-8")))
assert not re.search(r"\b(sorry|admit|axiom)\b", strip_lean(revised_path.read_text(encoding="utf-8")))
assert receipt["smallest_counterexample"]["entry"] != receipt["smallest_counterexample"]["candidate_rhs"]
print(json.dumps({"status":"PASS","disposition":"REFUTED_AS_STATED","lean_sha256":lean_hash,"audit_sha256":audit_hash,"revised_sha256":revised_hash,"revised_status":"COMPILED_PROOF","authority_effect":"NONE"}, sort_keys=True))
