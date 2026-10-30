"""Check CS lengths from the C simulators against c n.

Usage: python3 check_cs_large.py RANGE_FILE SINGLE_FILE
  RANGE_FILE   output of `deterministic_games N C` (lines "n L")
  SINGLE_FILE  output of `cs_single n1 n2 ...` (lines "n L ratio")
Prints JSON: deviation statistics of L - c n, the SHA-256 of both inputs, and
a check that the range file agrees with the pure-Python simulator for n <= 2000.
"""
import hashlib
import json
import sys
from decimal import Decimal, getcontext
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cs_constant import constants, cs_length  # noqa: E402


def main():
    rng, single = Path(sys.argv[1]), Path(sys.argv[2])
    getcontext().prec = 60
    _, _, c = constants()
    rows = [tuple(map(int, l.split()[:2])) for l in rng.read_text().split("\n") if l.strip()]
    devs = [(n, Decimal(L) - c * n) for n, L in rows]
    agree = all(cs_length(n) == L for n, L in rows if n <= 2000)
    singles = [tuple(map(int, l.split()[:2])) for l in single.read_text().split("\n") if l.strip()]
    out = {
        "schema": "cbmd.deterministic-zeckendorf.cs-large.v1",
        "range_sha256": hashlib.sha256(rng.read_bytes()).hexdigest(),
        "single_sha256": hashlib.sha256(single.read_bytes()).hexdigest(),
        "range_n_max": rows[-1][0],
        "range_python_agreement_n_le_2000": agree,
        "deviation_min": float(min(d for _, d in devs)),
        "deviation_max": float(max(d for _, d in devs)),
        "single_n_deviations": {str(n): round(float(Decimal(L) - c * n), 4) for n, L in singles},
        "status": "PASS" if agree else "FAIL",
        "nonclaims": ["deviations are observed; only O(log^2 n) is proved"],
        "authority_effect": "NONE",
    }
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if agree else 1


if __name__ == "__main__":
    raise SystemExit(main())
