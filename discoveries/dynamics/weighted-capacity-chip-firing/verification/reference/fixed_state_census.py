"""From a fixed initial state, which terminal states can capacity-blocked firing reach?

For every system with n <= 3, multiplicity <= 2, sink multiplicity <= 1 and
capacity <= d(v) + 1, and every admissible initial state, classify the set of
reachable capacity-terminal states: only the ordinary normal form, only states
that are not it, or both.  "Both" means firing order matters from that state.
This is exploratory evidence for the open fixed-initial-state question; it
proves nothing.
"""
from __future__ import annotations

import json
import sys
from itertools import product
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from characterize import cap_terminals, digraphs, od, ordinary_normal  # noqa: E402


def run(nmax=3):
    only_onf = only_bad = both = skipped = 0
    example = None
    for n in range(2, nmax + 1):
        for a, s in digraphs(n, 2, 1):
            for c in product(*(range(od(a, s, v) + 2) for v in range(n))):
                for x in product(*(range(ci + 1) for ci in c)):
                    onf = ordinary_normal(a, s, n, x)
                    T = cap_terminals(a, s, c, n, x)
                    if T is None or onf is None:
                        skipped += 1
                        continue
                    good, bad = onf in T, any(t != onf for t in T)
                    if good and not bad:
                        only_onf += 1
                    elif bad and not good:
                        only_bad += 1
                    else:
                        both += 1
                        if example is None:
                            example = {"arcs": [list(r) for r in a], "sink": list(s),
                                       "capacity": list(c), "initial": list(x),
                                       "ordinary_normal_form": list(onf),
                                       "reachable_terminals": sorted(map(list, T))}
    return {"schema": "cbmd.weighted-fixed-state-census.v1",
            "box": {"n": [2, nmax], "max_mult": 2, "max_sink_mult": 1, "capacity_slack": 1},
            "only_ordinary_normal_form": only_onf, "only_other_terminals": only_bad,
            "both": both, "skipped": skipped, "first_example_of_both": example,
            "nonclaims": ["exploratory census for an open question; no characterization is claimed"],
            "authority_effect": "NONE"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=1))
