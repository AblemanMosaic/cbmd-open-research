"""B5 cost theorem: enumeration route vs master-formula route for the integer amplitude.
argv[1] = package src dir (imports the frozen producer literal_numerator / parity / Meter, unchanged).

Declared bit-cost model (BCM-1):
  * integers carry their bit length; mul/div of x,y cost bits(x)*bits(y); add/sub cost max(bits);
  * an indicator test [swap(base,B)=y] costs Q coordinate comparisons; building swap(base,B) costs Q writes;
  * memoisation is NOT assumed: each amplitude is computed from scratch (the frozen producer does so).
Everything below is counted, not estimated; asymptotic statements are proved from the exact counts.
"""
import sys, json, itertools, time
from fractions import Fraction
from math import comb as _comb, log2
sys.path.insert(0, sys.argv[1])
from owner_sum import literal_numerator, parity, Meter

def comb(n, k):
    if k < 0 or (n >= 0 and k > n): return 0
    if n < 0: return (-1) ** k * _comb(-n + k - 1, k)
    return _comb(n, k)
def bits(x): return max(1, abs(int(x)).bit_length())

class BitMeter:
    def __init__(self): self.mul = self.div = self.add = 0; self.mul_bits = self.div_bits = self.add_bits = 0; self.peak = 0
    def m(self, x, y): self.mul += 1; self.mul_bits += bits(x) * bits(y); r = x * y; self.peak = max(self.peak, bits(r)); return r
    def d(self, x, y): self.div += 1; self.div_bits += bits(x) * bits(y); r = x // y; self.peak = max(self.peak, bits(r)); return r
    def a(self, x, y): self.add += 1; self.add_bits += max(bits(x), bits(y)); r = x + y; self.peak = max(self.peak, bits(r)); return r
    def json(self): return {'mul': self.mul, 'div': self.div, 'add': self.add, 'mul_bitops': self.mul_bits, 'div_bitops': self.div_bits, 'add_bitops': self.add_bits, 'peak_bits': self.peak}

def amplitude_closed(A, R, delta, f, bm):
    """n = 2^(R-1) * (-1)^A * sum_{k=0}^{d} C(N,k) C(A+d-k-1, d-k),  d=R-1-f, N=A+R-delta.
    Binomials computed incrementally: C(N,k) from C(N,k-1) by one mul and one exact div (generalised N<0 handled by sign)."""
    d = R - 1 - f; N = A + R - delta
    # C(N,k) incremental: C(N,0)=1; C(N,k)=C(N,k-1)*(N-k+1)/k  (valid for negative N as generalised binomial)
    # C(A+d-k-1, d-k): compute descending in k via the ascending sequence g_i = C(A+i-1, i), g_0=1, g_i = g_{i-1}*(A+i-1)/i
    g = [1]
    for i in range(1, d + 1):
        if A == 0: g.append(0)       # C(i-1,i)=0 for i>=1, C(-1,0)=1
        else: g.append(bm.d(bm.m(g[-1], A + i - 1), i))
    c = 1; total = 0
    for k in range(0, d + 1):
        if k:
            c = bm.d(bm.m(c, N - k + 1), k)
        total = bm.a(total, bm.m(c, g[d - k]))
    if A % 2: total = -total
    return bm.m(total, 2 ** (R - 1))

def enum_count(Q, R):
    """Exact number of (S,B) indicator tests the frozen producer performs per amplitude: sum_{j<R} C(Q-1,j) 2^j."""
    return sum(comb(Q - 1, j) * 2 ** j for j in range(R))

report = {'schema': 'cbmd.cost_theorem.v1', 'cost_model': 'BCM-1 (see docstring)'}

# ---- 1. exactness: closed route == frozen producer on a box; count enumeration tests against the formula ----
ok = bad = 0; cnt_ok = cnt_bad = 0
for Q in range(2, 8):
    types = list(itertools.product([0, 1], repeat=2 * Q))
    for A in range(0, 4):
        for R in range(1, min(5, Q + 2)):
            for u in types[:64]:
                D = [t for t in range(Q) if u[t] != u[Q + t]]
                for mask in itertools.product([0, 1], repeat=Q):
                    y = tuple(u[Q + t] if mask[t] else u[t] for t in range(Q)) + tuple(u[t] if mask[t] else u[Q + t] for t in range(Q))
                    E = [t for t in range(Q) if y[t] != u[Q + t]]
                    if not (1 <= len(E) <= R): continue
                    t = E[0]; m = Meter()
                    n_enum = literal_numerator(u, y, t, A, R, m)
                    n_closed = amplitude_closed(A, R, len(D), len(E) - 1, BitMeter())
                    if n_enum == n_closed: ok += 1
                    else: bad += 1
                    if m.counts['numerator_delta_terms'] == enum_count(Q, R): cnt_ok += 1
                    else: cnt_bad += 1
report['exactness'] = {'closed_eq_enum': ok, 'mismatch': bad, 'enum_count_formula_ok': cnt_ok, 'enum_count_formula_bad': cnt_bad}

# ---- 2. measured bit-cost of the closed route at native-like and small regimes ----
meas = []
for (A, R, Q) in [(17, 5, 80), (15, 8, 80), (7, 4, 40), (0, 3, 3), (1, 2, 3)]:
    worst = None
    for delta in range(1, Q + 1):
        for f in range(0, min(R, delta)):
            bm = BitMeter(); amplitude_closed(A, R, delta, f, bm); j = bm.json()
            if worst is None or j['mul_bitops'] + j['div_bitops'] > worst['mul_bitops'] + worst['div_bitops']: worst = {**j, 'delta': delta, 'f': f}
    meas.append({'A': A, 'R': R, 'Q': Q, 'closed_route_worst_case': worst,
                 'enumeration_indicator_tests_per_amplitude': enum_count(Q, R),
                 'enumeration_coordinate_ops_lower_bound': enum_count(Q, R) * Q,
                 'parity_solve_rational_cells_lower_bound': R * (R + 1)})
report['measurements'] = meas

# ---- 3. timing (diagnostic only, not a claim) ----
t0 = time.perf_counter();
for delta in range(1, 81):
    for f in range(5): amplitude_closed(17, 5, delta, f, BitMeter())
t_closed = time.perf_counter() - t0
t0 = time.perf_counter(); m = Meter()
u = (0,)*7 + (1,)*7; y = (1,0,0,0,0,0,0) + (0,1,1,1,1,1,1)   # Q=7, |D|=7, |E|=1
for _ in range(3): literal_numerator(u, y, 0, 17, 5, m)
t_enum7 = (time.perf_counter() - t0) / 3
report['timing_diagnostic'] = {'closed_400_amplitudes_Q80_seconds': round(t_closed, 4), 'enum_one_amplitude_Q7_seconds': round(t_enum7, 4), 'note': 'wall-clock, Python, diagnostic only; not part of any claim'}

# ---- 4. centered-line skip rate ----
def skip_rate(A, R):
    delta = 2 * A + R
    cand = sum(comb(delta, e) for e in range(1, R + 1))
    zero = sum(comb(delta, e) for e in range(1, R + 1) if (R - e) % 2 == 1)
    return {'A': A, 'R': R, 'delta': delta, 'orbit_candidates_1_le_E_le_R': cand, 'identically_zero_over_Z': zero, 'skip_fraction': round(zero / cand, 4)}
report['centered_skip'] = [skip_rate(A, R) for (A, R) in [(17, 5), (15, 8), (7, 4), (2, 4), (1, 3)]]
# plus 3-adic zeros on the central line via Kummer (even d): carries(d/2, A-1)
def carries3(a, b):
    c = 0; n = 0
    while a or b or c:
        s = a % 3 + b % 3 + c; c = 1 if s >= 3 else 0; n += c; a //= 3; b //= 3
    return n
for row in report['centered_skip']:
    A, R, delta = row['A'], row['R'], row['delta']
    extra = {}
    for t in (1, 2):
        z = 0
        for e in range(1, R + 1):
            d = R - e
            if d % 2 == 0 and A >= 1 and carries3(d // 2, A - 1) >= t: z += comb(delta, e)
        extra[f'additional_zero_mod_3^{t}'] = z
    row.update(extra)

print(json.dumps(report, indent=1))
