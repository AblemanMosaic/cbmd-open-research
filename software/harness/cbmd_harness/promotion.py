from __future__ import annotations

from typing import Any

from .canonical import root
from .refusals import Refusal


CEILINGS = [
    "OBSERVED",
    "FINITE_CHECK",
    "COMPILED_STATEMENT",
    "COMPILED_PROOF",
    "SOURCE_BOUND_PROOF",
    "REVIEW_READY",
]


def decide_promotion(request: dict[str, Any]) -> dict[str, Any]:
    required = {
        "question_id", "claim_ids", "requested_ceiling", "method", "terminal_status",
        "lean_escape_status", "source_correspondence_status", "adverse_status",
        "cold_replay_status", "repo_qualification_status", "evidence_roots",
    }
    if set(request) != required:
        raise Refusal("CBMD_PROMOTION_SCHEMA_REFUSED", "exact promotion request fields required")
    requested = request["requested_ceiling"]
    if requested not in CEILINGS:
        raise Refusal("CBMD_PROMOTION_CEILING_REFUSED", str(requested))
    if request["terminal_status"] != "PASS":
        raise Refusal("CBMD_PROMOTION_TERMINAL_REFUSED", request["terminal_status"])
    index = CEILINGS.index(requested)
    if request["method"] not in {"LEAN_LAKE", "PYTHON_EXACT", "UCM_NATIVE_PROOF", "PACKAGE_REPLAY", "REPO_QUALIFICATION", "CROSS_CHECK"}:
        raise Refusal("CBMD_PROMOTION_METHOD_REFUSED", str(request["method"]))
    if request["method"] == "UCM_NATIVE_PROOF":
        raise Refusal("CBMD_UCM_ADAPTER_UNBOUND", "No source-bound native proof adapter is installed.")
    if request["method"] == "PYTHON_EXACT" and index > CEILINGS.index("FINITE_CHECK"):
        raise Refusal("CBMD_FINITE_GENERALIZATION_REFUSED", requested)
    if index >= CEILINGS.index("COMPILED_PROOF") and request["lean_escape_status"] != "PASS":
        raise Refusal("CBMD_LEAN_ESCAPE_REFUSED", request["lean_escape_status"])
    if index >= CEILINGS.index("SOURCE_BOUND_PROOF") and request["source_correspondence_status"] != "PASS":
        raise Refusal("CBMD_SOURCE_CORRESPONDENCE_REFUSED", request["source_correspondence_status"])
    if index >= CEILINGS.index("SOURCE_BOUND_PROOF") and request["adverse_status"] != "PASS":
        raise Refusal("CBMD_ADVERSE_EVIDENCE_REFUSED", request["adverse_status"])
    if requested == "REVIEW_READY":
        if request["cold_replay_status"] != "PASS":
            raise Refusal("CBMD_COLD_REPLAY_REQUIRED", request["cold_replay_status"])
        if request["repo_qualification_status"] != "PASS":
            raise Refusal("CBMD_REPO_QUALIFICATION_REQUIRED", request["repo_qualification_status"])
    if not request["claim_ids"] or not request["evidence_roots"]:
        raise Refusal("CBMD_PROMOTION_EVIDENCE_INCOMPLETE", "claim identities and evidence roots required")
    if not isinstance(request["evidence_roots"], list) or not all(
        isinstance(item, str) and len(item) == 64 and all(char in "0123456789abcdef" for char in item)
        for item in request["evidence_roots"]
    ):
        raise Refusal("CBMD_PROMOTION_ROOT_REFUSED", "SHA-256 evidence roots required")
    decision_body = {
        "schema": "cbmd.claim-promotion-decision.v1",
        "question_id": request["question_id"],
        "claim_ids": request["claim_ids"],
        "ceiling": requested,
        "evidence_roots": request["evidence_roots"],
        "status": "PASS",
        "authority_effect": "NONE",
        "nonclaims": ["NOVELTY", "PUBLICATION", "REVIEWER_APPROVAL", "INDEPENDENT_VERIFICATION"],
    }
    return {**decision_body, "decision_root": root(decision_body)}
