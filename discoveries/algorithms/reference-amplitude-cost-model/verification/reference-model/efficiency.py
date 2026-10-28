"""Algorithmic efficiency theorems T1-T3 for the reference model (argv[1] = package src).
All routes are checked EXACTLY against the frozen producer source_row on a box; costs under BCM-1 / ring-op counts.
"""
import sys, json, itertools
from pathlib import Path
from fractions import Fraction
from math import comb as _comb
sys.path.insert(0, sys.argv[1])
from owner_sum import source_row, Ring, Meter, trim, literal_numerator
from common import Refusal

def comb(n, k):
    if k < 0 or (n >= 0 and k > n): return 0
    if n < 0: return (-1) ** k * _comb(-n + k - 1, k)
    return _comb(n, k)
def bits(x): return max(1, abs(int(x)).bit_length())

# ---------------- T1: spectrum table ----------------
def spectrum_table(A, R, Q, meter):
    """T[delta][f] = n(A,R,delta,f) for 1<=delta<=Q, 0<=f<min(R,delta). O(Q R^2) big-int ops (master formula per entry)."""
    T = {}
    for delta in range(1, Q + 1):
        for f in range(0, min(R, delta)):
            d = R - 1 - f; N = A + R - delta
            g = [1]
            for i in range(1, d + 1): g.append(0 if A == 0 else (g[-1] * (A + i - 1)) // i); meter['mul'] += 1; meter['div'] += 1
            c = 1; tot = 0
            for k in range(d + 1):
                if k: c = (c * (N - k + 1)) // k; meter['mul'] += 1; meter['div'] += 1
                tot += c * g[d - k]; meter['mul'] += 1; meter['add'] += 1
            T[(delta, f)] = (-1) ** A * tot * 2 ** (R - 1); meter['mul'] += 1
    return T

# ---------------- T2: row assembly from the table ----------------
def row_closed(u, y, A, R, ring, T, meter):
    """Closed row formula; requires 2^(R-1) and every s+1 for s in E to be units."""
    Q = len(u) // 2
    E = [t for t in range(Q) if y[t] != u[Q + t]]
    delta = sum(1 for t in range(Q) if u[t] != u[Q + t])
    out = (ring.norm(int(u == y)),)
    if not E or len(E) > R: return trim(out)
    inorbit = all({y[t], y[Q + t]} == {u[t], u[Q + t]} for t in range(Q))
    if not inorbit: return trim(out)
    n = T[(delta, len(E) - 1)]
    amp = ring.mul(ring.norm(n), ring.inv(ring.norm(2 ** (R - 1)))); meter['ring'] += 2
    prod = (ring.norm(1),)
    for s in E:                                        # prod *= (1 - x/(s+1))
        inv = ring.inv(ring.norm(s + 1)); meter['ring'] += 1
        prod = ring.poly_mul(prod, (ring.norm(1), ring.mul(ring.norm(-1), inv))); meter['ring'] += 2 * len(prod)
    phi = tuple(ring.add(ring.norm(1 if i == 0 else 0), ring.mul(ring.norm(-1), c)) for i, c in enumerate(prod))  # 1 - prod
    meter['ring'] += 2 * len(phi)
    corr = tuple(ring.mul(ring.norm(-1), ring.mul(amp, c)) for c in phi); meter['ring'] += 2 * len(phi)
    return trim(ring.poly_add(out, corr))

report = {'schema': 'cbmd.efficiency.v2'}
# exactness of T2 against frozen source_row on a box, rationals and Z/25
ok = bad = 0; ref_ring_ops = 0; new_ring_ops = 0; ref_enum = 0
for Q in (1, 2, 3, 4):
    types = list(itertools.product([0, 1], repeat=2 * Q))
    for A in (0, 1, 2):
        for R in (1, 2, 3):
            for mod in (None, 25):
                mt = {'mul': 0, 'div': 0, 'add': 0}; T = spectrum_table(A, R, Q, mt)
                for u in types[: (64 if Q == 4 else len(types))]:
                    for y in types:
                        if not all({y[t], y[Q + t]} == {u[t], u[Q + t]} for t in range(Q)): continue
                        m = Meter(); O = Ring(mod, m); a = trim(source_row(u, y, A, R, O, m))
                        ref_ring_ops += m.counts['ring_add'] + m.counts['ring_mul'] + m.counts['ring_inverse']; ref_enum += m.counts['numerator_delta_terms']
                        m2 = {'ring': 0}; O2 = Ring(mod, Meter()); b = row_closed(u, y, A, R, O2, T, m2); new_ring_ops += m2['ring']
                        if a == b: ok += 1
                        else: bad += 1
report['T2_exactness'] = {'rows_equal': ok, 'mismatch': bad, 'reference_ring_ops_total': ref_ring_ops, 'reference_enumeration_tests_total': ref_enum, 'closed_ring_ops_total': new_ring_ops}

# Explicit unit-boundary controls. The equality box above has Q<=4, so Z/25
# never encounters the nonunit node factor 5.
unit_controls = []
for label, modulus, A, R, Q, u, y in [
    ('node_5_nonunit_mod_25', 25, 1, 1, 5, (0,0,0,0,0,1,1,1,1,1), (1,1,1,1,0,0,0,0,0,1)),
    ('denominator_2_nonunit_mod_8', 8, 1, 2, 1, (0,1), (0,1)),
]:
    mt = {'mul': 0, 'div': 0, 'add': 0}; T = spectrum_table(A, R, Q, mt)
    try:
        row_closed(u, y, A, R, Ring(modulus, Meter()), T, {'ring': 0})
        refused = False
    except Refusal as ex:
        refused = str(ex) == 'NONUNIT'
    unit_controls.append({'case': label, 'modulus': modulus, 'status': 'PASS' if refused else 'FAIL', 'expected': 'NONUNIT_REFUSAL'})
report['T2_unit_hypotheses'] = {
    'required_units': ['2^(R-1)', 's+1 for every s in E'],
    'adverse_controls': unit_controls,
    'status': 'PASS' if all(row['status'] == 'PASS' for row in unit_controls) else 'FAIL'
}

# T1 cost at native-like regimes, and the per-row enumeration cost it replaces
def enum_tests(Q, R): return sum(comb(Q - 1, j) * 2 ** j for j in range(R))
rows = []
for (A, R, Q) in [(17, 5, 80), (15, 8, 80), (7, 4, 40)]:
    mt = {'mul': 0, 'div': 0, 'add': 0}; T = spectrum_table(A, R, Q, mt)
    rows.append({'A': A, 'R': R, 'Q': Q, 'table_entries': len(T), 'table_bigint_ops': mt, 'peak_bits': max(bits(v) for v in T.values()),
                 'per_amplitude_enumeration_tests_replaced': enum_tests(Q, R), 'distinct_targets_sharing_table': f'all 2^{2*Q} targets and all orbit columns'})
report['T1_table'] = rows

# T3: row-centric all-owners pass vs owner-centric candidate lookups (exact counts)
def live_columns(delta, R, A):
    """orbit columns with 1<=|E|<=R and nonzero amplitude (centered line excluded by parity when |D|=2A+R)."""
    tot = 0
    for e in range(1, R + 1):
        if delta == 2 * A + R and (R - e) % 2 == 1: continue
        tot += comb(delta, e)
    return tot + 1   # + the diagonal
t3 = []
for (A, R, Q) in [(17, 5, 80), (15, 8, 80), (7, 4, 40)]:
    for delta in (R + 1, 2 * A + R, Q // 2, Q):
        if delta > Q: continue
        lc = live_columns(delta, R, A)
        t3.append({'A': A, 'R': R, 'Q': Q, 'delta': delta, 'live_columns_incl_diagonal': lc,
                   'row_centric_cost': f'{lc} row assemblies + {lc} owner lookups (all nonzero owner sums at once)',
                   'owner_centric_cost': '|V| candidate constructions (Q coordinate tests each) + |V| vertex lookups + <= |V| row assemblies',
                   'row_centric_wins_when': f'|V| > {lc}'})
report['T3_crossover'] = t3
rendered = json.dumps(report, indent=1) + '\n'
if len(sys.argv) > 2:
    Path(sys.argv[2]).write_text(rendered, encoding='utf-8', newline='\n')
    print(json.dumps({'status': 'WRITTEN', 'output': sys.argv[2], 'schema': report['schema']}))
else:
    print(rendered, end='')
