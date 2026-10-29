"""Usage: python software/reference/evaluate.py A R delta f"""

from __future__ import annotations

import argparse
from dataclasses import asdict
import json

if __package__:
    from .cbmd_reference import master_numerator
else:
    from cbmd_reference import master_numerator


def main() -> None:
    parser = argparse.ArgumentParser(description="Exact master numerator and BCM-1 arithmetic counts")
    parser.add_argument("A", type=int)
    parser.add_argument("R", type=int)
    parser.add_argument("delta", type=int, help="active-set cardinality at the native bridge")
    parser.add_argument("f", type=int, help="mismatch cardinality minus one at the native bridge")
    args = parser.parse_args()
    try:
        result = master_numerator(args.A, args.R, args.delta, args.f)
    except ValueError as error:
        parser.error(str(error))
    print(json.dumps({
        "schema": "cbmd.reference.scalar.v1",
        "input": {"A": args.A, "R": args.R, "delta": args.delta, "f": args.f},
        **asdict(result),
        "count_scope": "BCM1_SCALAR_ARITHMETIC_ONLY",
        "claim_boundary": "PYTHON_EVALUATION_NOT_LEAN_REPLAY_OR_SPEEDUP",
    }, sort_keys=True, separators=(",", ":")))


if __name__ == "__main__":
    main()
