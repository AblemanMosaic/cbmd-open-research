"""Render the README discovery tables from DISCOVERIES.json."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "DISCOVERIES.json"
README = ROOT / "README.md"
BEGIN = "<!-- BEGIN GENERATED DISCOVERY INDEX -->"
END = "<!-- END GENERATED DISCOVERY INDEX -->"


def cell(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def link(row: dict[str, object]) -> str:
    return f"[{cell(row['title'])}]({cell(row['path'])}/README.md)"


def status(row: dict[str, object]) -> str:
    return "<br>".join(f"`{cell(value)}`" for value in row["status"])


def blocker_summary(row: dict[str, object]) -> str:
    blockers = row.get("promotion_blockers", [])
    if not blockers:
        return "None"
    return "; ".join(cell(value) for value in blockers)


def table(rows: list[dict[str, object]], include_blockers: bool) -> list[str]:
    if include_blockers:
        output = [
            "| ID | Discovery | Claim standing | Stage | Next obligation | Promotion blockers |",
            "|---|---|---|---|---|---|",
        ]
        for row in rows:
            output.append(
                "| `{id}` | {title} | {status} | `{stage}` | {next} | {blockers} |".format(
                    id=cell(row["id"]),
                    title=link(row),
                    status=status(row),
                    stage=cell(row["pipeline_stage"]),
                    next=cell(row["next_obligation"]),
                    blockers=blocker_summary(row),
                )
            )
        return output

    output = [
        "| ID | Discovery | Claim standing | Most valuable open question |",
        "|---|---|---|---|",
    ]
    for row in rows:
        output.append(
            "| `{id}` | {title} | {status} | {next} |".format(
                id=cell(row["id"]),
                title=link(row),
                status=status(row),
                next=cell(row["next_obligation"]),
            )
        )
    return output


def render(registry: dict[str, object]) -> str:
    rows = registry["discoveries"]
    review_ready = [row for row in rows if row["pipeline_stage"] in {"REVIEW_READY", "RELEASED"}]
    candidates = [row for row in rows if row["pipeline_stage"] in {"CLAIM_BOUND", "QUALIFYING"}]
    closed = [row for row in rows if row["pipeline_stage"] == "CLOSED"]

    lines = [BEGIN, "", "### Current review-ready discoveries", ""]
    lines.extend(table(review_ready, include_blockers=False) if review_ready else ["None."])
    lines.extend(["", "### Candidate pipeline", ""])
    lines.extend(table(candidates, include_blockers=True) if candidates else ["No candidates are currently admitted."])
    if closed:
        lines.extend(["", "### Closed, refuted, or superseded lines", ""])
        lines.extend(table(closed, include_blockers=True))
    lines.extend(["", END])
    return "\n".join(lines)


def replace_generated(readme: str, generated: str) -> str:
    if readme.count(BEGIN) != 1 or readme.count(END) != 1:
        raise ValueError("README must contain exactly one discovery-index marker pair")
    before, remainder = readme.split(BEGIN, 1)
    _, after = remainder.split(END, 1)
    return before + generated + after


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    args = parser.parse_args()

    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    current = README.read_text(encoding="utf-8")
    expected = replace_generated(current, render(registry))
    if args.check:
        if current != expected:
            print("README_DISCOVERY_INDEX_DRIFT", file=sys.stderr)
            return 1
        print(json.dumps({"status": "PASS", "discoveries": len(registry["discoveries"])}))
        return 0
    README.write_text(expected, encoding="utf-8", newline="\n")
    print(json.dumps({"status": "WRITTEN", "discoveries": len(registry["discoveries"])}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
