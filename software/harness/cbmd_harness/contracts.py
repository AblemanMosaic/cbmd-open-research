from __future__ import annotations

import re
from pathlib import Path
from typing import Any

from .canonical import load_json, root
from .refusals import Refusal


ROOT_RE = re.compile(r"^[0-9a-f]{64}$")
ID_RE = re.compile(r"^[A-Z][A-Z0-9_.:-]*$")


def require_exact_keys(value: dict[str, Any], required: set[str], optional: set[str], label: str) -> None:
    keys = set(value)
    missing = sorted(required - keys)
    extra = sorted(keys - required - optional)
    if missing:
        raise Refusal("CBMD_SCHEMA_MISSING", f"{label}:{','.join(missing)}")
    if extra:
        raise Refusal("CBMD_SCHEMA_EXTRA", f"{label}:{','.join(extra)}")


def require_id(value: Any, label: str) -> str:
    if not isinstance(value, str) or not ID_RE.fullmatch(value):
        raise Refusal("CBMD_ID_REFUSED", label)
    return value


def verify_authority(authority: dict[str, Any]) -> None:
    require_exact_keys(
        authority,
        {"schema", "authority_id", "standing", "authority_effect", "allowed_effects", "allowed_execution_roots", "excluded_effects", "source"},
        set(),
        "authority",
    )
    if authority["authority_effect"] != "NONE":
        raise Refusal("CBMD_AUTHORITY_EFFECT_REFUSED", "authority_effect must remain NONE")
    if not isinstance(authority["allowed_execution_roots"], list) or not all(
        isinstance(item, str) and Path(item).is_absolute() for item in authority["allowed_execution_roots"]
    ):
        raise Refusal("CBMD_EXECUTION_ROOT_SPEC_REFUSED", "roots must be explicit absolute project paths")
    excluded = set(authority["excluded_effects"])
    required = {"PUBLICATION", "PUBLIC_REPOSITORY", "RELEASE", "REVIEWER_CONTACT", "NOVELTY_CLAIM"}
    if not required.issubset(excluded):
        raise Refusal("CBMD_AUTHORITY_EXCLUSION_REFUSED", "mandatory exclusions missing")


def verify_lattice(lattice: dict[str, Any]) -> None:
    require_exact_keys(
        lattice,
        {"schema", "lattice_id", "version", "standing", "authority_effect", "nodes", "edges", "known_gaps"},
        set(),
        "lattice",
    )
    if lattice["authority_effect"] != "NONE":
        raise Refusal("CBMD_LATTICE_AUTHORITY_REFUSED", "authority effect")
    node_ids: set[str] = set()
    for node in lattice["nodes"]:
        require_exact_keys(node, {"id", "kind", "description", "standing", "realizations", "claim_ceiling"}, set(), "node")
        node_id = require_id(node["id"], "node.id")
        if node_id in node_ids:
            raise Refusal("CBMD_LATTICE_DUPLICATE_NODE", node_id)
        node_ids.add(node_id)
    for edge in lattice["edges"]:
        require_exact_keys(edge, {"from", "to", "relation"}, set(), "edge")
        if edge["from"] not in node_ids or edge["to"] not in node_ids:
            raise Refusal("CBMD_LATTICE_DANGLING_EDGE", f"{edge['from']}->{edge['to']}")


def verify_rsc(contract: dict[str, Any]) -> None:
    required = {
        "schema", "contract_id", "contract_version", "subject", "possibility", "axes",
        "constraints", "capabilities", "selection", "lowering", "evidence", "authority",
    }
    require_exact_keys(contract, required, {"description", "objectives", "preferred_regions", "revision"}, "rsc")
    require_id(contract["contract_id"], "contract_id")
    if contract["schema"] != "cbmd.realization-space-contract.v1":
        raise Refusal("CBMD_RSC_SCHEMA_REFUSED", str(contract["schema"]))
    subject = contract["subject"]
    require_exact_keys(
        subject,
        {"subject_id", "subject_schema", "authority_owner", "source_roots", "preserved_identity", "forbidden_overrides"},
        {"coordinate_frame"},
        "rsc.subject",
    )
    require_id(subject["subject_id"], "subject.subject_id")
    require_id(subject["authority_owner"], "subject.authority_owner")
    if not subject["source_roots"] or not subject["preserved_identity"]:
        raise Refusal("CBMD_RSC_SUBJECT_INCOMPLETE", "source roots and preserved identity required")
    if not contract["axes"]:
        raise Refusal("CBMD_RSC_EMPTY_AXES", "axes")
    axis_ids: set[str] = set()
    for axis in contract["axes"]:
        require_exact_keys(
            axis,
            {"id", "label", "description", "value_type", "domain", "default", "ownership", "mutability", "continuity", "authority_effect"},
            set(),
            "axis",
        )
        axis_id = require_id(axis["id"], "axis.id")
        if axis_id in axis_ids:
            raise Refusal("CBMD_RSC_DUPLICATE_AXIS", axis_id)
        axis_ids.add(axis_id)
        if axis["authority_effect"] != "NONE":
            raise Refusal("CBMD_RSC_AXIS_AUTHORITY_REFUSED", axis_id)
        values = axis["domain"].get("values") if isinstance(axis["domain"], dict) else None
        if values is not None and axis["default"] not in values:
            raise Refusal("CBMD_RSC_DEFAULT_REFUSED", axis_id)
        if axis["ownership"] == "DERIVED" and axis["mutability"] != "DERIVED":
            raise Refusal("CBMD_RSC_DERIVED_MUTABILITY_REFUSED", axis_id)
    constraint_ids: set[str] = set()
    for constraint in contract["constraints"]:
        require_exact_keys(
            constraint,
            {"id", "kind", "severity", "expression", "explanation", "refusal_code"},
            {"expression_language"},
            "constraint",
        )
        constraint_id = require_id(constraint["id"], "constraint.id")
        require_id(constraint["refusal_code"], "constraint.refusal_code")
        if constraint_id in constraint_ids:
            raise Refusal("CBMD_RSC_DUPLICATE_CONSTRAINT", constraint_id)
        constraint_ids.add(constraint_id)
        if constraint["severity"] not in {"HARD", "ADVISORY"}:
            raise Refusal("CBMD_RSC_CONSTRAINT_SEVERITY_REFUSED", constraint_id)
    capabilities = contract["capabilities"]
    if len(capabilities) != len(set(capabilities)):
        raise Refusal("CBMD_RSC_DUPLICATE_CAPABILITY", "capabilities")
    required_capabilities = {"ENUMERATE", "VALIDATE", "NORMALIZE", "SELECT", "LOWER", "REALIZE", "EXPLAIN", "RECEIPT"}
    if not required_capabilities.issubset(set(capabilities)):
        raise Refusal("CBMD_RSC_CAPABILITY_INCOMPLETE", "required lifecycle capability missing")
    targets = contract["lowering"].get("targets", [])
    if not targets:
        raise Refusal("CBMD_RSC_TARGETS_EMPTY", "lowering.targets")
    target_ids: set[str] = set()
    for target in targets:
        require_exact_keys(
            target,
            {"target_id", "adapter_version", "required_capabilities", "preservation_criteria", "known_losses", "fallbacks"},
            {"runtime_family", "supported_region", "axis_mapping", "refusal_conditions"},
            "target",
        )
        target_id = require_id(target["target_id"], "target.target_id")
        if target_id in target_ids:
            raise Refusal("CBMD_RSC_DUPLICATE_TARGET", target_id)
        target_ids.add(target_id)
        if not target["preservation_criteria"]:
            raise Refusal("CBMD_RSC_TARGET_PRESERVATION_EMPTY", target_id)
    allowed_results = set(contract["lowering"].get("allowed_results", []))
    if not {"EXACT", "REFUSED"}.issubset(allowed_results):
        raise Refusal("CBMD_RSC_LOWERING_RESULT_INCOMPLETE", "EXACT and REFUSED required")
    evidence = contract["evidence"]
    if not evidence.get("required_roots") or not evidence.get("required_fields") or not evidence.get("non_claims"):
        raise Refusal("CBMD_RSC_EVIDENCE_INCOMPLETE", "roots, fields, and nonclaims required")
    if contract["authority"].get("authority_effect") != "NONE":
        raise Refusal("CBMD_RSC_AUTHORITY_REFUSED", "authority_effect")
    if contract["authority"].get("self_admission") is not False:
        raise Refusal("CBMD_RSC_SELF_ADMISSION_REFUSED", "self_admission")


def load_and_verify_specs(root_path: Path) -> dict[str, str]:
    authority_path = root_path / "spec" / "CBMD-AUTHORITY.json"
    lattice_path = root_path / "spec" / "CBMD-CAPABILITY-LATTICE.json"
    rsc_path = root_path / "spec" / "CBMD-REALIZATION-SPACE-CONTRACT.json"
    authority = load_json(authority_path)
    lattice = load_json(lattice_path)
    rsc = load_json(rsc_path)
    verify_authority(authority)
    verify_lattice(lattice)
    verify_rsc(rsc)
    return {
        "authority_root": root(authority),
        "lattice_root": root(lattice),
        "realization_space_root": root(rsc),
    }
