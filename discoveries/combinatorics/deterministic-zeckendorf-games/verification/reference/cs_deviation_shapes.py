"""How D(n) = L_CS(n) - c n depends on the Zeckendorf SHAPE of n.

The dossier records "D(n) is negative and grows like -0.42 log_phi n".  That
coefficient is the value for typical n; it is not universal.  This tool
measures D/log_phi n along families of fixed shape, and searches two-term
n = F_m + F_k for the smallest |D|/log_phi n, which is the quantity that would
have to tend to 0 for the (unproved) Theta(log n) statement to fail pointwise.

Fibonacci indexing here is the standard one, fib[1] = fib[2] = 1; the dossier's
own indexing for the game shifts this, so only ratios are compared.

Usage: cs_deviation_shapes.py [M] [--json]    (M = largest Fibonacci index)
"""
import json
import sys
from decimal import Decimal, getcontext
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cs_exact import fast  # noqa: E402


def setup(M):
    # n < F_{M+1} has about 0.209 M decimal digits, so c needs that many digits plus slack
    # for D = L_CS(n) - c n to be exact to far better than 1.
    getcontext().prec = max(120, M + 60)
    phi = (1 + Decimal(5).sqrt()) / 2
    # 1/f_{2k-1} decays like phi^{-2k}, i.e. 0.418 decimal digits per term
    terms = int(getcontext().prec / 0.418) + 10
    fib = [0, 1]
    while len(fib) < max(4 * M + 40, 2 * terms + 6):
        fib.append(fib[-1] + fib[-2])
    c = sum(1 / Decimal(fib[2 * k - 1]) for k in range(1, terms)) - 1 / phi
    return phi, fib, c


def main():
    M = int(sys.argv[1]) if len(sys.argv) > 1 and sys.argv[1].isdigit() else 180
    phi, fib, c = setup(M)
    lp = phi.ln()

    def D(n):
        return float(Decimal(fast(n)) - c * n)

    def L(n):
        return float(Decimal(n).ln() / lp)

    shapes = {}

    def record(name, n):
        shapes[name] = {'L': round(L(n), 3), 'D': round(D(n), 4),
                        'ratio': round(D(n) / L(n), 5)}

    record('F_m', fib[M])
    record('F_m_plus_1', fib[M] + 1)
    record('two_F_m', 2 * fib[M])
    record('F_m_minus_1', fib[M] - 1)
    for g in (2, 3, 4, 6):
        t = max(2, (M - 2) // g)
        record(f'density_1_over_{g}', sum(fib[g * j + 2] for j in range(t)))

    ratios = [abs(v['ratio']) for v in shapes.values()]
    spread = max(ratios) / min(ratios)

    # two-term minimum: the candidate for a bounded family
    twoterm = {}
    for m in (M // 3, 2 * M // 3, M):
        best = None
        for k in range(4, m - 1):
            n = fib[m] + fib[k]
            d = abs(D(n))
            if best is None or d < best[0]:
                best = (d, k, n)
            if best is not None and best[0] == 0:
                break
        d, k, n = best
        twoterm[str(m)] = {'min_abs_D': round(d, 4), 'at_k': k,
                           'k_over_m': round(k / m, 4), 'L': round(L(n), 3),
                           'ratio': round(d / L(n), 5)}

    ms = sorted(twoterm, key=int)
    grows = all(twoterm[ms[i]]['min_abs_D'] < twoterm[ms[i + 1]]['min_abs_D']
                for i in range(len(ms) - 1))
    never_zero = all(v['min_abs_D'] > 0 for v in twoterm.values()) and \
        all(v['D'] != 0 for v in shapes.values())
    # the point of the table: one coefficient does not describe every n
    not_universal = spread > 2
    out = {'M': M, 'shapes': shapes, 'spread_of_abs_ratio': round(spread, 4),
           'coefficient_not_universal': not_universal,
           'two_term_minimum': twoterm,
           'two_term_min_abs_D_increasing_in_m': grows,
           'deviation_never_zero': never_zero,
           'ok': bool(not_universal and grows and never_zero)}
    if '--json' in sys.argv:
        print(json.dumps(out, indent=1))
    else:
        for k, v in shapes.items():
            print(f"  {k:<22} L={v['L']:>9.3f} D={v['D']:>11.4f} ratio={v['ratio']:>9.5f}")
        print(f"  spread of |ratio| = {spread:.4f}  (not universal: {not_universal})")
        for m in ms:
            v = twoterm[m]
            print(f"  two-term m={m:>5}: min|D|={v['min_abs_D']:>9.4f} at k={v['at_k']:>4}"
                  f" (k/m={v['k_over_m']:.3f}) ratio={v['ratio']:>8.5f}")
        print(f"  min|D| increasing in m: {grows};  deviation never 0: {never_zero}")
        print("OK" if out['ok'] else "UNEXPECTED")
    return 0 if out['ok'] else 1


if __name__ == '__main__':
    sys.exit(main())
