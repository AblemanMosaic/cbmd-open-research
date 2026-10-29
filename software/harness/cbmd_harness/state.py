from __future__ import annotations

from pathlib import Path
from typing import Any

from .canonical import load_json, root, write_json
from .refusals import Refusal
from .ledger import Ledger


def refresh_state(root_path: Path, candidate: dict[str, Any]) -> dict[str, Any]:
    required = {
        "cycle_id", "question_id", "status", "claim_ids", "evidence_roots",
        "substantive_advance", "consecutive_no_advance_cycles", "next_action", "known_remainder",
    }
    if set(candidate) != required:
        raise Refusal("CBMD_STATE_SCHEMA_REFUSED", "exact state fields required")
    if not isinstance(candidate["consecutive_no_advance_cycles"], int) or candidate["consecutive_no_advance_cycles"] < 0:
        raise Refusal("CBMD_STATE_COUNTER_REFUSED", "consecutive_no_advance_cycles")
    state_path = root_path / "state" / "CURRENT.json"
    predecessor = None
    if state_path.exists():
        old = load_json(state_path)
        predecessor = old["state_root"]
        if old["cycle_id"] == candidate["cycle_id"]:
            old_body = {k: v for k, v in old.items() if k != "state_root"}
            proposed_body = {"schema": "cbmd.discovery-state.v1", "predecessor": old["predecessor"], **candidate}
            if root(old_body) == root(proposed_body):
                Ledger(root_path / "runtime" / "ledger").append_once("DISCOVERY_STATE", old["cycle_id"], old["state_root"])
                return old
    body = {"schema": "cbmd.discovery-state.v1", "predecessor": predecessor, **candidate}
    state = {**body, "state_root": root(body)}
    if state_path.exists():
        history = root_path / "state" / "history" / f"{load_json(state_path)['state_root']}.json"
        if not history.exists():
            write_json(history, load_json(state_path))
    write_json(state_path, state)
    Ledger(root_path / "runtime" / "ledger").append_once("DISCOVERY_STATE", state["cycle_id"], state["state_root"])
    return state
