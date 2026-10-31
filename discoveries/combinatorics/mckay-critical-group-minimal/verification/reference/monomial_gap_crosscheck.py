"""Independent GAP recomputation of the monomial enumeration (monomial_enum.py output).

For every enumerated group of order <= MAXORDER, rebuilds G from explicit 3x3 matrices over cyclotomic
fields and recomputes |G|, P = prod_{c != 1} (3 - chi(c)) (exact) and |G^ab| with GAP's own
conjugacy classes.  Prints 'CROSSCHECK <count> true' when all agree.

usage: python3 monomial_gap_crosscheck.py ENUM.jsonl [MAXORDER=220]
"""
import json, os, subprocess, sys, tempfile

TAU = (1, 0, 2)


def gap_file(path, maxorder):
    lines = ['SizeScreen([4000,100]);;', 'res := [];;']
    for k, l in enumerate(open(path)):
        r = json.loads(l)
        if r['order'] > maxorder:
            continue
        n = r['A_order']
        (a1, b1), (a2, b2) = r['A_hnf']

        def diag(a, b):
            return f"DiagonalMat([E({n})^{a % n}, E({n})^{b % n}, E({n})^{(-a - b) % n}])"
        gens = [diag(a1, b1), diag(a2, b2), "[[0,0,1],[1,0,0],[0,1,0]]"]   # P_s: e_i -> e_{s(i)}, s = (1,2,0)
        if r['type'] == 'D':
            M, d = r['M'], r['t_exponents']
            m = [['0'] * 3 for _ in range(3)]
            for i in range(3):
                m[TAU[i]][i] = f"E({M})^{d[TAU[i]]}"
            gens.append('[' + ','.join('[' + ','.join(row) + ']' for row in m) + ']')
        lines.append(f"G := Group({', '.join(gens)});; t := CharacterTable(G);; "
                     f"v := List(ConjugacyClasses(t), c -> TraceMat(Representative(c)));;")
        lines.append(f"P := Product(List([2..Length(v)], c -> 3 - v[c]));; "
                     f"Add(res, [{k}, Size(G) = {r['order']}, P = {r['P']}, Product(AbelianInvariants(G)) = {r['Gab']}]);;")
    lines.append('Print("CROSSCHECK ", Length(res), " ", ForAll(res, x -> x[2] and x[3] and x[4]), "\\n");')
    lines.append('Print("FAILURES ", Filtered(res, x -> not (x[2] and x[3] and x[4])), "\\n"); QUIT;')
    return '\n'.join(lines) + '\n'


def main():
    path = sys.argv[1]
    maxorder = int(sys.argv[2]) if len(sys.argv) > 2 else 220
    with tempfile.TemporaryDirectory() as tmp:
        f = os.path.join(tmp, 'x.g')
        open(f, 'w').write(gap_file(path, maxorder))
        out = subprocess.run(['gap', '-q', f], stdin=subprocess.DEVNULL, capture_output=True, text=True).stdout
    print(out.strip())
    return 0 if ' true' in out.split('CROSSCHECK')[-1].splitlines()[0] else 1


if __name__ == '__main__':
    sys.exit(main())
