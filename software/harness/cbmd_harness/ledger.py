from __future__ import annotations

import json
import os
from pathlib import Path
from typing import Any

from .canonical import canonical_bytes, load_json, root, write_json
from .refusals import Refusal


GENESIS = "0" * 64


class Ledger:
    def __init__(self, runtime_root: Path):
        self.root = runtime_root
        self.journal = runtime_root / "EVENTS.jsonl"
        self.head_path = runtime_root / "HEAD.json"

    def verify(self) -> dict[str, Any]:
        previous = GENESIS
        count = 0
        if self.journal.exists():
            with self.journal.open("r", encoding="utf-8") as handle:
                for line_number, line in enumerate(handle, start=1):
                    try:
                        event = json.loads(line)
                    except json.JSONDecodeError as exc:
                        raise Refusal("CBMD_LEDGER_JSON_REFUSED", f"line {line_number}:{exc}") from exc
                    expected_keys = {"schema", "sequence", "previous", "event_type", "operation_id", "payload_root", "event_root"}
                    if set(event) != expected_keys:
                        raise Refusal("CBMD_LEDGER_SHAPE_REFUSED", f"line {line_number}")
                    if event["sequence"] != count + 1 or event["previous"] != previous:
                        raise Refusal("CBMD_LEDGER_CHAIN_REFUSED", f"line {line_number}")
                    body = {key: value for key, value in event.items() if key != "event_root"}
                    if root(body) != event["event_root"]:
                        raise Refusal("CBMD_LEDGER_ROOT_REFUSED", f"line {line_number}")
                    previous = event["event_root"]
                    count += 1
        if self.head_path.exists():
            head = load_json(self.head_path)
            if head != {"schema": "cbmd.ledger-head.v1", "count": count, "head": previous}:
                raise Refusal("CBMD_LEDGER_HEAD_REFUSED", "head does not match journal")
        elif count:
            raise Refusal("CBMD_LEDGER_HEAD_MISSING", "journal exists without head")
        return {"count": count, "head": previous}

    def append(self, event_type: str, operation_id: str, payload_root: str) -> dict[str, Any]:
        state = self.verify()
        body = {
            "schema": "cbmd.ledger-event.v1",
            "sequence": state["count"] + 1,
            "previous": state["head"],
            "event_type": event_type,
            "operation_id": operation_id,
            "payload_root": payload_root,
        }
        event = dict(body)
        event["event_root"] = root(body)
        self.root.mkdir(parents=True, exist_ok=True)
        with self.journal.open("ab") as handle:
            handle.write(canonical_bytes(event) + b"\n")
            handle.flush()
            os.fsync(handle.fileno())
        write_json(self.head_path, {"schema": "cbmd.ledger-head.v1", "count": event["sequence"], "head": event["event_root"]})
        return event

    def append_once(self, event_type: str, operation_id: str, payload_root: str) -> dict[str, Any]:
        self.verify()
        if self.journal.exists():
            with self.journal.open("r", encoding="utf-8") as handle:
                for line in handle:
                    event = json.loads(line)
                    if event["event_type"] == event_type and event["operation_id"] == operation_id:
                        if event["payload_root"] != payload_root:
                            raise Refusal("CBMD_LEDGER_IDENTITY_CONFLICT", f"{event_type}:{operation_id}")
                        return event
        return self.append(event_type, operation_id, payload_root)
