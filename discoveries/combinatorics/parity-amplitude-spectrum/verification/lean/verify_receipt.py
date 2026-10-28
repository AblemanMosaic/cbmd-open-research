from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


HERE = Path(__file__).resolve().parent
DISCOVERY = HERE.parent.parent
SOURCE = HERE / "CenteredVanishingCore.lean"
RECEIPT = DISCOVERY / "evidence" / "LEAN_CENTERED_CORE_RECEIPT.json"


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
actual = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
assert actual == receipt["source"]["sha256"], "source hash mismatch"
assert receipt["operation"]["status"] == "PASS" and receipt["operation"]["exit_code"] == 0
assert receipt["claim_ceiling"] == "COMPILED_PROOF"
assert not re.search(r"\b(sorry|admit|axiom)\b", strip_lean(SOURCE.read_text(encoding="utf-8")))
print(json.dumps({"status":"PASS","source_sha256":actual,"claim_ceiling":"COMPILED_PROOF","authority_effect":"NONE"}, sort_keys=True))
