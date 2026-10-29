from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from .adapters import plan_lean, plan_python
from .canonical import root
from .contracts import load_and_verify_specs
from .courts import court, lean_escape_scan
from .evidence import health, verify_all
from .refusals import Refusal
from .runner import execute
from .promotion import decide_promotion
from .state import refresh_state
from .canonical import load_json, write_json
from .ledger import Ledger
from .recovery import recover_uncertain
from .workspace import initialize_workspace


def _emit(value: Any) -> None:
    print(json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False))


def _root_path() -> Path:
    return Path(__file__).resolve().parent.parent


def orient(root_path: Path) -> dict[str, Any]:
    roots = load_and_verify_specs(root_path)
    return {
        "schema": "cbmd.harness-orientation.v1",
        "system": "CBMD_GOVERNED_DISCOVERY_HARNESS",
        "version": "0.1.0",
        "standing": "LOCAL_CANDIDATE",
        "authority_effect": "NONE",
        **roots,
        "roles": ["GOVERNANCE_SUBSTRATE","EHM","HEADLESS_RUNNER","CTR","CRP","AIS","EVS","SAS"],
        "excluded_effects": ["PUBLICATION","PUBLIC_REPOSITORY","RELEASE","REVIEWER_CONTACT","NOVELTY_CLAIM"],
        "next_action": "Run court and verify; explicitly initialize a local workspace before executing a pinned request."
    }


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="cbmd")
    parser.add_argument("--workspace", type=Path, help="local contracts, runtime custody, and state directory")
    sub = parser.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init-workspace")
    init.add_argument("--path", required=True, type=Path)
    init.add_argument("--execution-root", action="append", required=True, type=Path)
    sub.add_parser("orient")
    sub.add_parser("verify")
    sub.add_parser("court")
    sub.add_parser("health")
    run = sub.add_parser("run")
    run.add_argument("request", type=Path)
    lean = sub.add_parser("plan-lean")
    lean.add_argument("--project", required=True, type=Path)
    lean.add_argument("--module", required=True)
    lean.add_argument("--out", type=Path)
    lean.add_argument("--question-id", default="CBMD.CURRENT")
    lean.add_argument("--claim-id", action="append", default=[])
    python = sub.add_parser("plan-python")
    python.add_argument("--script", required=True, type=Path)
    python.add_argument("--cwd", required=True, type=Path)
    python.add_argument("--out", type=Path)
    python.add_argument("--question-id", default="CBMD.LOCAL.PROBE")
    python.add_argument("--claim-id", action="append", default=[])
    scan = sub.add_parser("scan-lean")
    scan.add_argument("paths", nargs="+", type=Path)
    promote = sub.add_parser("promote")
    promote.add_argument("request", type=Path)
    promote.add_argument("--out", type=Path)
    state = sub.add_parser("state-refresh")
    state.add_argument("candidate", type=Path)
    recover = sub.add_parser("recover-uncertain")
    recover.add_argument("operation_id")
    recover.add_argument("--basis", required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    try:
        root_path = args.workspace.resolve(strict=True) if args.workspace is not None else _root_path()
        if args.command == "init-workspace":
            result = initialize_workspace(_root_path(), args.path, args.execution_root)
        elif args.command == "orient":
            result = orient(root_path)
        elif args.command == "verify":
            result = verify_all(root_path)
        elif args.command == "court":
            result = court(root_path, test_root=_root_path())
        elif args.command == "health":
            result = health(root_path)
        elif args.command == "run":
            result = execute(root_path, args.request.resolve(strict=True))
        elif args.command == "plan-lean":
            authority_id = load_json(root_path / "spec" / "CBMD-AUTHORITY.json")["authority_id"]
            result = plan_lean(args.project, args.module, args.out, args.question_id, args.claim_id, authority_id)
        elif args.command == "plan-python":
            authority_id = load_json(root_path / "spec" / "CBMD-AUTHORITY.json")["authority_id"]
            result = plan_python(args.script, args.cwd, args.out, args.question_id, args.claim_id, authority_id)
        elif args.command == "scan-lean":
            result = lean_escape_scan([path.resolve(strict=True) for path in args.paths])
        elif args.command == "promote":
            result = decide_promotion(load_json(args.request.resolve(strict=True)))
            if args.out is not None:
                write_json(args.out, result)
            Ledger(root_path / "runtime" / "ledger").append_once(
                "CLAIM_PROMOTION", "PROMOTION-" + result["decision_root"][:24].upper(), result["decision_root"]
            )
        elif args.command == "state-refresh":
            result = refresh_state(root_path, load_json(args.candidate.resolve(strict=True)))
        elif args.command == "recover-uncertain":
            result = recover_uncertain(root_path, args.operation_id, args.basis)
        else:
            raise AssertionError(args.command)
        _emit(result)
        return 0 if result.get("status", "PASS") in {"PASS", "HEALTHY", "DEGRADED", "ACTIVE", "PAUSED"} else 1
    except Refusal as exc:
        _emit(exc.as_dict())
        return 2
    except (OSError, ValueError, TypeError, KeyError) as exc:
        _emit({"status": "REFUSED", "code": "CBMD_INPUT_REFUSED", "detail": str(exc), "authority_effect": "NONE"})
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
