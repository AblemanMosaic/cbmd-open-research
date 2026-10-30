"""Exhaustive maximal length M(n) of the ordered Zeckendorf game versus the LGS length, n <= N (default 16)."""
import json
import sys
from functools import lru_cache
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lgs_constant import direct_lgs  # noqa: E402

sys.setrecursionlimit(100000)


def moves(a):
    out = []
    for p in range(len(a) - 1):
        x, y = a[p], a[p + 1]
        if x > y:
            out.append(a[:p] + (y, x) + a[p + 2:])
        if x == 1 and y == 1:
            out.append(a[:p] + (2,) + a[p + 2:])
        if x == y and x >= 2:
            out.append(a[:p] + ((1, 3) if x == 2 else (x - 2, x + 1)) + a[p + 2:])
        if y == x + 1:
            out.append(a[:p] + (x + 2,) + a[p + 2:])
    return out


@lru_cache(maxsize=None)
def M(a):
    m = moves(a)
    return 0 if not m else 1 + max(M(b) for b in m)


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    rows = {n: (M((1,) * n), direct_lgs(n)) for n in range(1, N + 1)}
    ok = all(a == b for a, b in rows.values())
    print(json.dumps({"n_max": N, "M_and_LGS": {str(k): v for k, v in rows.items()},
                      "status": "PASS" if ok else "FAIL", "authority_effect": "NONE"}, indent=1))
    raise SystemExit(0 if ok else 1)
