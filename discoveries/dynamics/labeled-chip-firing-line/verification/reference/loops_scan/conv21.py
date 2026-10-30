"""Converse scan for HMP Conjecture 21 (our observation, not in HMP): for S subset [LO,HI], |S|<=MAXSIZE,
n in 3..MAXN with n >= deg(0) (origin fires) and the Conjecture-21 condition FAILING, test whether
Z<S> fails to sort Delta^n.  usage: python3 conv21.py LO HI MAXSIZE MAXN OUTFILE  (resumable JSONL)"""
import itertools, json, os, subprocess, sys
from multiprocessing import Pool
from zs import stab_unlabeled, occ
HERE = os.path.dirname(os.path.abspath(__file__))
def job(a):
    S, n = a
    env = dict(os.environ, ZS_EARLY='1')
    out = subprocess.run([os.path.join(HERE, 'zsr_bin'), '1', str(n)] + [str(s) for s in S], capture_output=True, text=True, env=env)
    if out.returncode != 0: return S, n, 'ERROR:' + out.stderr.strip()
    return S, n, out.stdout.strip().split('\n')[-1].split()[1]
if __name__ == '__main__':
    lo, hi, maxsize, maxn, outfile = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    done = set()
    if os.path.exists(outfile):
        for l in open(outfile):
            r = json.loads(l); done.add((tuple(r['S']), r['n']))
    tasks = []
    for size in range(0, maxsize + 1):
        for S in itertools.combinations(range(lo, hi + 1), size):
            deg0 = 3 if 0 in S else 2
            for n in range(max(3, deg0), maxn + 1):
                a = occ(stab_unlabeled(n, set(S))); b = occ(stab_unlabeled(n - 1, set(S)))
                if not (a[0] < b[0] and a[1] > b[1]) and (S, n) not in done: tasks.append((S, n))
    tasks.sort(key=lambda x: x[1])
    print('pending', len(tasks), 'already', len(done), flush=True)
    with Pool(2) as p, open(outfile, 'a') as f:
        for S, n, res in p.imap_unordered(job, tasks, chunksize=4):
            f.write(json.dumps({'S': list(S), 'n': n, 'result': res}) + '\n'); f.flush()
            if res != 'FAIL': print('SORTS-WITHOUT-CONDITION', S, n, res, flush=True)
    print('finished', flush=True)
