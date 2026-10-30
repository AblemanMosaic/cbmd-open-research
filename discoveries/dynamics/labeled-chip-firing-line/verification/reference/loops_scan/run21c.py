"""Driver for HMP Conjecture 21 two-colour search using the C++ tester zs_bin.
usage: python3 run21c.py LO HI MAXSIZE MAXN OUTFILE
Enumerates S subset of [LO,HI] with |S|<=MAXSIZE, n in 2..MAXN, keeps the instances where the
unlabeled stabilization of n chips strictly extends that of n-1 chips on both ends, runs zs_bin,
and appends one JSON line per instance to OUTFILE (resumable: skips instances already logged).
"""
import itertools, json, os, subprocess, sys
from multiprocessing import Pool
from zs import stab_unlabeled, occ
HERE = os.path.dirname(os.path.abspath(__file__))
def job(a):
    S, n = a
    out = subprocess.run([os.path.join(HERE, 'zs_bin'), str(n)] + [str(s) for s in S],
                         capture_output=True, text=True)
    if out.returncode != 0:
        return S, n, 'ERROR:' + out.stderr.strip(), 0
    lines = out.stdout.strip().split('\n')
    states = sum(int(l.split()[1].split('=')[1]) for l in lines[:-1])
    return S, n, lines[-1].split()[1], states
if __name__ == '__main__':
    lo, hi, maxsize, maxn, outfile = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    done = set()
    if os.path.exists(outfile):
        for l in open(outfile):
            r = json.loads(l); done.add((tuple(r['S']), r['n']))
    tasks = []
    for size in range(0, maxsize + 1):
        for S in itertools.combinations(range(lo, hi + 1), size):
            for n in range(2, maxn + 1):
                a = occ(stab_unlabeled(n, set(S))); b = occ(stab_unlabeled(n - 1, set(S)))
                if a[0] < b[0] and a[1] > b[1] and (S, n) not in done:
                    tasks.append((S, n))
    tasks.sort(key=lambda x: x[1])  # small n first
    print('pending', len(tasks), 'already', len(done), flush=True)
    with Pool(2) as p, open(outfile, 'a') as f:
        for S, n, res, states in p.imap_unordered(job, tasks, chunksize=1):
            f.write(json.dumps({'S': list(S), 'n': n, 'result': res, 'states': states}) + '\n'); f.flush()
            if res != 'ok':
                print('NON-OK', S, n, res, flush=True)
    print('finished', flush=True)
