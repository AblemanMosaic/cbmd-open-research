"""Validate the extensible public-discovery tree using only the standard library."""
from __future__ import annotations

import json
from pathlib import Path, PurePosixPath
import sys


ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "DISCOVERIES.json"
VALID_STATES = {
    "CONJECTURE",
    "PROVISIONAL_WRITTEN_ARGUMENT",
    "EXACT_MODEL_VERIFIED",
    "GEOMETRIC_TRANSPORT_UNRESOLVED",
    "INDEPENDENTLY_REPRODUCED",
    "SPECIALIST_REVIEWED",
    "REVISED",
    "REFUTED",
    "SUPERSEDED",
}
REQUIRED_DIRS = ("argument", "explorer", "verification", "evidence", "review", "revisions")
PIPELINE_STAGES = {"INTAKE", "CLAIM_BOUND", "QUALIFYING", "REVIEW_READY", "RELEASED", "CLOSED"}


def fail(message: str) -> None:
    raise ValueError(message)


def safe_relative(value: str) -> PurePosixPath:
    path = PurePosixPath(value)
    if path.is_absolute() or not path.parts or any(part in ("", ".", "..") for part in path.parts):
        fail(f"unsafe registry path: {value!r}")
    return path


def main() -> int:
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    rows = registry.get("discoveries")
    if not isinstance(rows, list) or not rows:
        fail("discovery registry must contain at least one row")

    seen_ids: set[str] = set()
    seen_paths: set[str] = set()
    registered_claims: set[Path] = set()

    for row in rows:
        claim_id = row.get("id")
        if not isinstance(claim_id, str) or not claim_id.startswith("CBMD-"):
            fail(f"invalid claim id: {claim_id!r}")
        if claim_id in seen_ids:
            fail(f"duplicate claim id: {claim_id}")
        seen_ids.add(claim_id)

        relative = safe_relative(row.get("path", ""))
        if relative.as_posix() in seen_paths:
            fail(f"duplicate discovery path: {relative}")
        seen_paths.add(relative.as_posix())
        if relative.parts[:1] != ("discoveries",):
            fail(f"discovery must live below discoveries/: {relative}")

        discovery = ROOT.joinpath(*relative.parts)
        if not discovery.is_dir():
            fail(f"missing discovery directory: {relative}")
        for required in ("README.md", "CLAIM.json"):
            if not (discovery / required).is_file():
                fail(f"missing {relative / required}")
        for required in REQUIRED_DIRS:
            if not (discovery / required).is_dir():
                fail(f"missing required directory: {relative / required}")

        claim_path = discovery / "CLAIM.json"
        claim = json.loads(claim_path.read_text(encoding="utf-8"))
        registered_claims.add(claim_path.resolve())
        if claim.get("id") != claim_id:
            fail(f"claim id mismatch at {relative}")
        if claim.get("field") != row.get("field") or claim.get("slug") != row.get("slug"):
            fail(f"field/slug mismatch at {relative}")
        claim_states = claim.get("status")
        if not isinstance(claim_states, list) or not claim_states:
            fail(f"claim status absent at {relative}")
        unknown = set(claim_states) - VALID_STATES
        if unknown:
            fail(f"unknown claim states at {relative}: {sorted(unknown)}")
        if claim_states != row.get("status"):
            fail(f"registry and claim status differ at {relative}")
        nonclaims = claim.get("nonclaims")
        if not isinstance(nonclaims, list) or not nonclaims or any(not isinstance(value, str) or not value.strip() for value in nonclaims):
            fail(f"explicit nonclaims absent at {relative}")
        if row.get("pipeline_stage") not in PIPELINE_STAGES:
            fail(f"invalid pipeline stage at {relative}")
        if not isinstance(row.get("next_obligation"), str) or not row["next_obligation"].strip():
            fail(f"next obligation absent at {relative}")
        blockers = row.get("promotion_blockers")
        if not isinstance(blockers, list) or any(not isinstance(value, str) or not value.strip() for value in blockers):
            fail(f"invalid promotion blockers at {relative}")
        checks = claim.get("checks", [])
        if not isinstance(checks, list):
            fail(f"checks must be a list at {relative}")
        check_ids: set[str] = set()
        for check in checks:
            if not isinstance(check, dict) or set(check) != {"id", "command", "required"}:
                fail(f"invalid check declaration at {relative}")
            if not isinstance(check["id"], str) or not check["id"] or check["id"] in check_ids:
                fail(f"invalid or duplicate check id at {relative}")
            check_ids.add(check["id"])
            if not isinstance(check["command"], list) or not check["command"] or any(not isinstance(value, str) or not value for value in check["command"]):
                fail(f"invalid check command at {relative}")
            if not isinstance(check["required"], bool):
                fail(f"invalid check requirement at {relative}")
        if row["pipeline_stage"] in {"REVIEW_READY", "RELEASED"} and not checks:
            fail(f"qualified pipeline stage requires declared checks at {relative}")
        if claim.get("authority_effect") != "NONE":
            fail(f"public candidate cannot claim authority effect at {relative}")

    actual_claims = {path.resolve() for path in (ROOT / "discoveries").rglob("CLAIM.json")}
    if actual_claims != registered_claims:
        fail("registered and on-disk CLAIM.json files differ")

    folded: dict[str, Path] = {}
    for path in ROOT.rglob("*"):
        if ".git" in path.parts or not path.is_file():
            continue
        rel = path.relative_to(ROOT)
        key = rel.as_posix().casefold()
        if key in folded:
            fail(f"case-colliding paths: {folded[key]} and {rel}")
        folded[key] = rel
        if "farris" in rel.as_posix().casefold():
            fail(f"reviewer-associated public filename refused: {rel}")
        if path.suffix.lower() in {".md", ".html", ".json", ".js", ".cjs", ".py", ".yml", ".yaml"}:
            text = path.read_text(encoding="utf-8")
            blocked_public_phrases = (
                "FARRIS" + "_EXPLORER",
                "Prepared for David Michael " + "Farris",
            )
            if any(phrase in text for phrase in blocked_public_phrases):
                fail(f"reviewer-associated public text refused: {rel}")

    result = {
        "status": "PASS",
        "schema": registry.get("schema"),
        "repository_standing": registry.get("repository_standing"),
        "discovery_count": len(rows),
        "claim_ids": sorted(seen_ids),
        "checked_files": len(folded),
        "authority_effect": "NONE",
    }
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print(json.dumps({"status": "FAIL", "error": str(exc)}, sort_keys=True), file=sys.stderr)
        sys.exit(1)
