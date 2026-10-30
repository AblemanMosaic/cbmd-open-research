"""How L_CS(n) - c n grows, using the exact polylog length (cs_exact.py).

Prints JSON: the deviation at n = 10^k and summary statistics over 100 random
n in [10^e, 10^(e+1)) for e in (10, 20, 40), with seed 5. Observation only.
"""
import json
import math
import random
import sys
from decimal import Decimal, getcontext
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cs_exact import fast  # noqa: E402

getcontext().prec = 150
phi = (1 + Decimal(5).sqrt()) / 2
fib = [0, 1]
while len(fib) < 1000:
    fib.append(fib[-1] + fib[-2])
c = sum(1 / Decimal(fib[2 * k - 1]) for k in range(1, 450)) - 1 / phi


def dev(n):
    return float(Decimal(fast(n)) - c * n)


random.seed(5)
out = {"at_powers_of_10": {str(k): round(dev(10 ** k), 3) for k in (3, 6, 9, 12, 15, 20, 30, 40, 60)},
       "random_samples": {}}
for e in (10, 20, 40):
    ds = [dev(random.randrange(10 ** e, 10 ** (e + 1))) for _ in range(100)]
    lp = (e + 0.5) * math.log(10) / math.log((1 + 5 ** 0.5) / 2)
    out["random_samples"][str(e)] = {"min": round(min(ds), 3), "max": round(max(ds), 3),
                                     "mean": round(sum(ds) / len(ds), 3),
                                     "mean_over_log_phi_n": round(sum(ds) / len(ds) / lp, 4)}
out["observation"] = "L_CS(n) - c n is negative and grows like a constant times log n (about -0.42 log_phi n), so it appears unbounded; not proved"
out["authority_effect"] = "NONE"
print(json.dumps(out, indent=1, sort_keys=True))
