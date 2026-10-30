"""Scaling scan: does r(Z<S>) sort Delta^{rn} iff Z<S> sorts Delta^n?  S in [-3,3], |S|<=3,
2<=n<=11, r in {1,2,3} with rn <= 24.  Writes JSONL to argv[1]."""
import itertools, json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
with open(sys.argv[1], 'w') as f:
    for size in range(0, 4):
        for S in itertools.combinations(range(-3, 4), size):
            for n in range(2, 12):
                res = {}
                for r in (1, 2, 3):
                    if r * n > 24: continue
                    out = subprocess.run([os.path.join(HERE, 'zsr_bin'), str(r), str(r * n)] + [str(s) for s in S], capture_output=True, text=True)
                    res[str(r)] = out.stdout.strip().split('\n')[-1].split()[1]
                f.write(json.dumps({'S': list(S), 'n': n, 'results': res}) + '\n')
