"""Assemble evidence/mckay_scans.json from raw GAP outputs (copies them into evidence/raw/).

usage: python3 build_evidence.py SCAN_ALL_LE40_N5 SCAN_NONAB_LE71_N6 SCAN_NONAB_LE150_N3 ATLAS_OUT SO3_OUT
                                PRIM_OUT TYPEB_OUT MONOMIAL_JSONL CROSSCHECK_OUT MONOTONICITY_OUT
"""
import json, os, re, shutil, sys
HERE = os.path.dirname(os.path.abspath(__file__))
EV = os.path.normpath(os.path.join(HERE, '..', '..', 'evidence'))
os.makedirs(os.path.join(EV, 'raw'), exist_ok=True)


def scan_summary(path, name, rawname, params):
    shutil.copy(path, os.path.join(EV, 'raw', rawname))
    lines = open(path).read().splitlines()
    done = [l for l in lines if l.startswith('DONE')]
    hits = [l for l in lines if l.startswith('HIT')]
    orders = sorted({int(re.search(r'\[ (\d+),', l).group(1)) for l in done})
    n3 = {}
    for l in hits:
        if ' n=3 ' in l:
            gid = re.search(r'\[ \d+, \d+ \]', l).group(0)
            n3[gid] = n3.get(gid, 0) + 1
    return {
        'name': name, 'raw': 'raw/' + rawname, 'params': params,
        'groups': len(done),
        'orders_covered': [orders[0], orders[-1]] if orders else [],
        'representations': sum(int(re.search(r'reps=(\d+)', l).group(1)) for l in done),
        'hits': len(hits),
        'hits_n2': sum(' n=2 ' in l for l in hits),
        'hits_n3': sum(' n=3 ' in l for l in hits),
        'hits_n_ge4': sum(int(re.search(r' n=(\d+) ', l).group(1)) >= 4 for l in hits),
        'n3_hit_groups': n3,
        'mismatches': sum(l.startswith('MISMATCH') for l in lines),
        'below': sum(l.startswith('BELOW') for l in lines),
        'snf_failures': sum(('snf_match=true' not in l) for l in hits),
    }


scan_all, scan_nonab, scan_n3, atlas, so3, prim, typeb, mono, cross, monot = sys.argv[1:11]
scans = [
    scan_summary(scan_all, 'all groups of order <= 40, n <= 5', 'scan_all_le40_n5.txt',
                 {'ORDERS': '2..40', 'DMAX': 5, 'SKIPAB': False}),
    scan_summary(scan_nonab, 'non-abelian groups of order <= 71, n <= 6', 'scan_nonabelian_le71_n6.txt',
                 {'ORDERS': '2..71', 'DMAX': 6, 'SKIPAB': True}),
    scan_summary(scan_n3, 'non-abelian groups of order <= 150, n = 3', 'scan_nonabelian_le150_n3.txt',
                 {'ORDERS': '2..150', 'DMAX': 3, 'SKIPAB': True}),
]
shutil.copy(atlas, os.path.join(EV, 'raw', 'atlas_n8.txt'))
expected = {('A5', 'n=3'): 2, ('2.A5', 'n=2'): 2}
at = []
for l in open(atlas):
    if l.startswith('DONE'):
        m = re.match(r'DONE (\S+) \|G\|=(\d+) DMAX=(\d+) faithful_SL_reps=(\d+) hits=(\d+) min_ratio=(\S+)', l)
        nm = m.group(1)
        hits = [h for h in open(atlas) if h.startswith('HIT ' + nm + ' ')]
        exp = sum(v for (g, _), v in expected.items() if g == nm)
        at.append({'name': nm, 'order': int(m.group(2)), 'dmax': int(m.group(3)), 'representations': int(m.group(4)),
                   'hits': int(m.group(5)), 'min_ratio_K_over_Gab': m.group(6),
                   'unexpected_hits': abs(int(m.group(5)) - exp)})
shutil.copy(so3, os.path.join(EV, 'raw', 'so3.txt'))
so3l = [l for l in open(so3) if l.startswith('SO3 ')]
shutil.copy(prim, os.path.join(EV, 'raw', 'primitive_sl3.txt'))
priml = [re.sub(r'\s+', ' ', l.strip()) for l in open(prim) if l.startswith('PRIM ')]
shutil.copy(typeb, os.path.join(EV, 'raw', 'typeB_exceptional.txt'))
tbl = [re.sub(r'\s+', ' ', l.strip()) for l in open(typeb) if l.startswith('TYPEB ')]
shutil.copy(mono, os.path.join(EV, 'raw', 'monomial_le76.jsonl'))
mrec = [json.loads(l) for l in open(mono)]
shutil.copy(cross, os.path.join(EV, 'raw', 'monomial_gap_crosscheck.txt'))
ctext = open(cross).read()
shutil.copy(monot, os.path.join(EV, 'raw', 'monotonicity_le60_d4.txt'))
mline = [l for l in open(monot) if l.startswith('TESTS')][0].split()
out = {
    'schema': 'cbmd.mckay-minimal.evidence.v2',
    'monotonicity_search': {'params': {'ORDMAX': 60, 'D1': 4, 'D2': 4, 'nonabelian': True}, 'tests': int(mline[1]), 'violations': int(mline[3]), 'equalities': int(mline[5])},
    'typeB_exceptional': {'groups': len(tbl), 'rows': tbl,
                          'minimal_iff_trivial_constituent': all(('minimal=true' in l) == ('trivial_constituent=1' in l) for l in tbl)},
    'monomial': {'groups': len(mrec), 'type_C': sum(r['type'] == 'C' for r in mrec), 'type_D': sum(r['type'] == 'D' for r in mrec),
                 'max_rounding_error': max(r['P_rounding_error'] for r in mrec),
                 'minimal': [{k: r[k] for k in ('type', 'A_order', 'order', 'trivial_multiplicity', 'real_character')}
                             for r in mrec if r['P'] == r['order'] * r['Gab']],
                 'gap_crosscheck': ctext.strip()},
    'gap': 'GAP 4.12.1, SmallGrp 1.5.3, CTblLib 1.3.7',
    'scans': scans,
    'atlas': at,
    'so3': {'groups': len(so3l), 'all_ok': all('ok=true' in l for l in so3l),
            'iso_cases': [l.split()[1] for l in so3l if 'iso=true' in l]},
    'primitive_sl3': priml,
}
json.dump(out, open(os.path.join(EV, 'mckay_scans.json'), 'w'), indent=1)
open(os.path.join(EV, 'mckay_scans.json'), 'a').write('\n')
for s in scans:
    print(s['name'], {k: s[k] for k in ('groups', 'representations', 'hits', 'hits_n_ge4', 'mismatches', 'below', 'snf_failures')})
print('atlas groups', len(at), 'unexpected', sum(a['unexpected_hits'] for a in at))
print('so3', out['so3']['groups'], out['so3']['all_ok'])
print('typeB', out['typeB_exceptional']['groups'], out['typeB_exceptional']['minimal_iff_trivial_constituent'])
print('monomial', out['monomial']['groups'], out['monomial']['minimal'])
print('crosscheck', ctext.strip().splitlines()[0])
