"""Check imported record custody and bindings; never present it as Lean replay."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys


ROOT = Path(__file__).resolve().parent.parent
SNAPSHOT = "evidence/iterations/bootstrap-2026-10/SNAPSHOT.json"
HEX64 = re.compile(r"[0-9a-f]{64}\Z")


def require(condition: bool, diagnostic: str) -> None:
    if not condition:
        raise ValueError(diagnostic)


def repository_file(relative: str) -> Path:
    require(isinstance(relative, str) and "\\" not in relative and ":" not in relative,
            "unsafe repository path")
    parts = PurePosixPath(relative)
    require(not parts.is_absolute() and bool(parts.parts) and ".." not in parts.parts,
            "unsafe repository path")
    result = ROOT.joinpath(*parts.parts).resolve()
    require(ROOT in result.parents, "path escapes repository")
    require(result.is_file(), "required snapshot input absent: " + relative)
    return result


def verify() -> dict[str, object]:
    manifest = json.loads(repository_file(SNAPSHOT).read_text(encoding="utf-8"))
    require(manifest["schema"] == "cbmd.open-research.iteration-snapshot.v1",
            "snapshot schema mismatch")
    require(manifest["research_status"] == "PAUSED", "research pause not preserved")
    require(manifest["full_proof_replay_from_this_checkout"] == "NOT_YET_PACKAGED",
            "custody checker cannot certify proof replay")
    require(manifest["authority_effect"] == "NONE", "invalid authority effect")
    require(bool(HEX64.fullmatch(manifest["source_state_root"])), "invalid state root")

    rows = manifest["artifacts"]
    require(isinstance(rows, list) and bool(rows), "empty artifact set")
    paths: set[str] = set()
    decision_claims: set[str] = set()
    decisions: dict[str, dict[str, object]] = {}
    summaries: list[dict[str, object]] = []
    state = None
    for row in rows:
        relative = row["path"]
        require(relative not in paths, "duplicate artifact path")
        paths.add(relative)
        require(bool(HEX64.fullmatch(row["sha256"])), "invalid artifact digest")
        source = repository_file(relative)
        require(hashlib.sha256(source.read_bytes()).hexdigest() == row["sha256"],
                "snapshot digest mismatch: " + relative)
        record = json.loads(source.read_text(encoding="utf-8"))
        role = row["role"]
        require(role in {"promotion_decision", "historical_summary", "cycle_state"},
                "unknown artifact role")
        if role == "promotion_decision":
            require(record["status"] == "PASS" and record["authority_effect"] == "NONE",
                    "unexpected promotion standing")
            require(bool(HEX64.fullmatch(record["decision_root"])), "invalid decision root")
            require(record["decision_root"] not in decisions, "duplicate decision root")
            decisions[record["decision_root"]] = record
            decision_claims.update(record["claim_ids"])
        elif role == "historical_summary":
            summaries.append(record)
        else:
            require(state is None, "multiple cycle states")
            state = record

    require(state is not None and state["status"] == "PAUSED", "paused state absent")
    require(state["state_root"] == manifest["source_state_root"], "state binding mismatch")
    require(set(state["evidence_roots"]) & set(decisions), "state decision link absent")
    for summary in summaries:
        root = summary.get("promotion_decision_root")
        if root is not None:
            require(root in decisions, "summary decision absent")
            promoted = set(decisions[root]["claim_ids"])
            require(bool(promoted) and promoted <= set(summary["claim_ids"]),
                    "decision claims absent from linked summary")

    registry = json.loads(repository_file("DISCOVERIES.json").read_text(encoding="utf-8"))
    discoveries = {row["id"]: row for row in registry["discoveries"]}
    seen: set[str] = set()
    for binding in manifest["discovery_bindings"]:
        discovery_id = binding["discovery_id"]
        require(discovery_id in discoveries and discovery_id not in seen,
                "invalid discovery binding")
        seen.add(discovery_id)
        require(set(binding["claim_ids"]) <= decision_claims,
                "discovery claim absent from copied decisions")
        claim = json.loads(repository_file(discoveries[discovery_id]["path"] + "/CLAIM.json")
                           .read_text(encoding="utf-8"))
        require(claim["ledger_binding"]["snapshot"] == SNAPSHOT,
                "discovery points to another snapshot")
        require(claim["ledger_binding"]["claim_ids"] == binding["claim_ids"],
                "discovery and snapshot claims differ")
        require(discoveries[discovery_id]["pipeline_stage"] in
                {"QUALIFYING", "REVIEW_READY", "RELEASED"},
                "historical binding has an incompatible current pipeline stage")

    return {
        "status": "PASS", "schema": "cbmd.open-research.snapshot-custody-check.v1",
        "snapshot_id": manifest["snapshot_id"], "artifacts_checked": len(paths),
        "discovery_bindings_checked": len(seen), "scope": "RECORD_CUSTODY_AND_BINDINGS_ONLY",
        "ancillary_summary_claims_promoted": False,
        "lean_recompiled": False, "source_ledger_reconstructed": False,
        "independent_verification": False, "authority_effect": "NONE",
        "current_pipeline_stage_promoted_by_snapshot": False,
    }


if __name__ == "__main__":
    try:
        print(json.dumps(verify(), sort_keys=True))
    except (KeyError, OSError, TypeError, ValueError) as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc), "authority_effect": "NONE"},
                         sort_keys=True), file=sys.stderr)
        sys.exit(1)
