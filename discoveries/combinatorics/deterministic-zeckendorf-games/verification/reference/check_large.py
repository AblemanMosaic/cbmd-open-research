"""Check the SS representation, closed form and block law on C-simulator output.

    cc -O2 -o deterministic_games deterministic_games.c
    ./deterministic_games 120000 S > ss.txt
    python -I -B check_large.py ss.txt
"""
from __future__ import annotations
import hashlib, json, sys
from fractions import Fraction
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from zeckendorf_games import FIB, zeck_indices, load_rep, rep_eval  # noqa: E402

def main():
    path = Path(sys.argv[1])
    raw = path.read_bytes()
    L = {}
    for line in raw.decode().split("\n"):
        if line.strip():
            n, l = map(int, line.split())
            L[n] = l
    S = {0: 0}
    S.update({n: L[n] - (n - len(zeck_indices(n))) for n in L})
    rep = load_rep(Path(__file__).resolve().parent / "ss_linrep.json")
    bad = [n for n in L if rep_eval(rep, n) != S[n]]
    fib_bad = []
    for k in range(1, len(FIB)):
        if FIB[k + 1] > max(L):
            break
        t = FIB[k + 1] - Fraction(2 * k * k + 8 * k + 15 + (-1) ** k, 8)
        if S[FIB[k]] != t or S[FIB[k] - 1] != S[FIB[k]]:
            fib_bad.append(k)
    blocks, block_bad = {}, 0
    for k in range(4, len(FIB)):
        if FIB[k] > max(L):
            break
        for m in range(FIB[k - 1]):
            n = FIB[k] + m
            if n > max(L):
                break
            d = S[n] - S[FIB[k]] - S[m]
            if (k % 2, m) in blocks and blocks[(k % 2, m)] != d:
                block_bad += 1
            blocks[(k % 2, m)] = d
    out = {"data_sha256": hashlib.sha256(raw).hexdigest(), "n_max": max(L),
           "representation_mismatches": len(bad), "fibonacci_closed_form_failures": fib_bad,
           "block_law_violations": block_bad,
           "status": "PASS" if not bad and not fib_bad and not block_bad else "FAIL"}
    print(json.dumps(out, indent=1))
    return 0 if out["status"] == "PASS" else 1

if __name__ == "__main__":
    raise SystemExit(main())
