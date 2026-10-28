from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


DISCOVERY = Path(__file__).resolve().parent.parent
RECEIPT = DISCOVERY / "evidence" / "PARITY_REFLECTION_RECEIPT.json"


def strip_lean(text: str) -> str:
    out: list[str] = []
    i = depth = 0
    in_string = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                i += 2
                continue
            i += 1
            continue
        if not in_string and pair == "/-":
            depth = 1
            i += 2
            continue
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
assert receipt["status"] == "PASS"
assert receipt["standing"] == "COMPILED_PROOF"
proof = receipt["compiled_proof"]
path = DISCOVERY / proof["path"]
digest = hashlib.sha256(path.read_bytes()).hexdigest()
assert digest == proof["sha256"]
source = strip_lean(path.read_text(encoding="utf-8"))
assert not re.search(r"\b(sorry|admit|axiom)\b", source)
for theorem in (
    "eval_parityPolynomialQ_nat",
    "natDegree_parityPolynomialQ_lt",
    "parityPolynomialQ_reflect",
    "parityInterpolantCore_reflect",
):
    assert re.search(rf"\btheorem\s+{theorem}\b", source)
print(json.dumps({
    "authority_effect": "NONE",
    "decision_root": proof["decision_root"],
    "sha256": digest,
    "status": "PASS",
    "terminal_root": proof["terminal_root"],
}, sort_keys=True))
