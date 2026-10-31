"""Minimal critical groups of McKay quivers (BKR Question 6.11): gates.

Requires GAP 4 (tested with 4.12.1) with the SmallGrp and CTblLib packages on PATH as `gap`.
Without GAP every GAP-backed gate FAILS (fail closed); nothing is skipped silently.

Gates (each required):
  * SO3_PROPOSITION: for G~ <= SU(2) cyclic, binary dihedral (orders up to 48), 2T, 2O, 2I, with
    G = G~/{+-1} <= SO(3): |K(rho)| = |G~^ab| (BKR n = 2), |K(gamma)| = 2^(u-1) |G~^ab|
    (Proposition 3), and K(gamma) ~= (G^ab)^ exactly in the cases predicted by Theorem 4;
    Gaetz's formula agrees with the Smith normal form throughout;
  * PRIMITIVE_SL3: for the primitive finite subgroups of SL_3(C) (Blichfeldt types E-L), and every
    faithful 3-dimensional irreducible character with trivial determinant, K ~= (G^ab)^ only for
    A5; Gaetz's formula agrees with the Smith normal form;
  * SCAN_SMALL: all groups of order <= 24 (abelian included), all faithful representations into
    SL_n without trivial constituent, n <= 5: the cases K ~= (G^ab)^ are exactly the conjectured
    ones (no MISMATCH), no case has |K| < |G^ab| (BKR), and each hit is confirmed by Smith normal
    form;
  * ATLAS_SMALL: ATLAS tables A5, 2.A5, L2(7), S5, A6, 2.A6 with n <= 6: hits are exactly the two
    3-dimensional representations of A5 and the two 2-dimensional ones of 2.A5;
  * EVIDENCE_SUMMARY: evidence/mckay_scans.json records zero mismatches and zero BKR violations in
    the larger scans, and its counts match its raw files.
"""
from __future__ import annotations
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
EVIDENCE = os.path.normpath(os.path.join(HERE, '..', '..', 'evidence'))


def run_gap(driver_lines, outname):
    """Run GAP on a temporary driver in HERE; return the text written to OUT (or None)."""
    if shutil.which('gap') is None:
        return None
    with tempfile.TemporaryDirectory() as tmp:
        out = os.path.join(tmp, outname)
        drv = os.path.join(tmp, 'driver.g')
        with open(drv, 'w') as fh:
            fh.write(f'OUT := "{out}";; PrintTo(OUT, "");\n')
            fh.write('\n'.join(driver_lines) + '\n')
        proc = subprocess.run(['gap', '-q', drv], cwd=HERE, capture_output=True, text=True, timeout=3600)
        if not os.path.exists(out):
            return None
        text = open(out).read()
        if proc.returncode not in (0,):
            text += f'\nGAP_EXIT {proc.returncode}\n{proc.stderr[-2000:]}'
        return text


def run_gap_stdout(driver_lines):
    if shutil.which('gap') is None:
        return None
    with tempfile.TemporaryDirectory() as tmp:
        drv = os.path.join(tmp, 'driver.g')
        with open(drv, 'w') as fh:
            fh.write('\n'.join(driver_lines) + '\n')
        proc = subprocess.run(['gap', '-q', drv], cwd=HERE, capture_output=True, text=True, timeout=3600)
        return proc.stdout


def gate_so3():
    txt = run_gap(['MMAX := 12;;', 'Read("so3.g");'], 'so3.out')
    if txt is None:
        return {'pass': False, 'reason': 'GAP unavailable or produced no output'}
    lines = [l for l in txt.splitlines() if l.startswith('SO3 ')]
    expected = 2 * 11 + 3
    bad = [l for l in lines if 'ok=true' not in l]
    iso = sorted(l.split()[1] for l in lines if 'iso=true' in l)
    want_iso = sorted([f'C{m}' for m in range(2, 13)] + [f'D{2 * m}' for m in range(3, 13, 2)] + ['A4', 'A5'])
    ok = len(lines) == expected and not bad and 'SO3_ALL_OK true' in txt and iso == want_iso
    return {'pass': ok, 'groups': len(lines), 'failures': bad[:3], 'iso_cases': iso}


def gate_primitive():
    txt = run_gap(['Read("prim.g");'], 'prim.out')
    if txt is None:
        return {'pass': False, 'reason': 'GAP unavailable or produced no output'}
    lines = [l for l in txt.splitlines() if l.startswith('PRIM ')]
    types = sorted({l.split()[1].split('#')[0] for l in lines})
    want = sorted(['A5', 'L2(7)', '3.A6', 'A5xC3', 'L2(7)xC3', 'Hessian108', 'Hessian216', 'Hessian648'])
    iso = sorted({l.split()[1].split('#')[0] for l in lines if 'iso=true' in l})
    agree = all('agree=true' in l for l in lines)
    ok = types == want and iso == ['A5'] and agree and len(lines) > 0
    rows = [re.sub(r'\s+', ' ', l) for l in lines]
    return {'pass': ok, 'characters': len(lines), 'types': types, 'iso_types': iso, 'rows': rows}


def gate_scan():
    txt = run_gap(['ORDERS := [2..24];; DMAX := 5;; SKIPAB := false;;', 'Read("mckay_scan.g");'], 'scan.out')
    if txt is None:
        return {'pass': False, 'reason': 'GAP unavailable or produced no output'}
    done = [l for l in txt.splitlines() if l.startswith('DONE')]
    hits = [l for l in txt.splitlines() if l.startswith('HIT')]
    mism = [l for l in txt.splitlines() if l.startswith('MISMATCH')]
    below = [l for l in txt.splitlines() if l.startswith('BELOW')]
    reps = sum(int(re.search(r'reps=(\d+)', l).group(1)) for l in done)
    snf_ok = all('snf_match=true' in l and 'pred=true' in l for l in hits)
    n3 = sorted({re.search(r'\[ (\d+), (\d+) \]', l).group(0) for l in hits if ' n=3 ' in l})
    ok = len(done) > 0 and reps > 0 and not mism and not below and snf_ok and len(hits) > 0 \
        and '[ 12, 3 ]' in n3 and '[ 6, 1 ]' in n3
    return {'pass': ok, 'groups': len(done), 'representations': reps, 'hits': len(hits),
            'n3_hit_groups': n3, 'mismatches': mism[:5], 'below': below[:5]}


def gate_atlas():
    out = run_gap_stdout(['NAMES := ["A5", "2.A5", "L2(7)", "S5", "A6", "2.A6"];; DMAX := 6;;',
                          'Read("atlas_scan.g");'])
    if out is None:
        return {'pass': False, 'reason': 'GAP unavailable'}
    hits = [re.sub(r'\s+', ' ', l) for l in out.splitlines() if l.startswith('HIT')]
    done = [l for l in out.splitlines() if l.startswith('DONE')]
    summary = sorted((h.split()[1], h.split()[2]) for h in hits)
    ok = len(done) == 6 and summary == [('2.A5', 'n=2'), ('2.A5', 'n=2'), ('A5', 'n=3'), ('A5', 'n=3')]
    return {'pass': ok, 'groups': len(done), 'hits': hits}


def gate_evidence():
    path = os.path.join(EVIDENCE, 'mckay_scans.json')
    if not os.path.exists(path):
        return {'pass': False, 'reason': 'missing evidence/mckay_scans.json'}
    ev = json.load(open(path))
    ok = True
    for s in ev['scans']:
        ok &= s['mismatches'] == 0 and s['below'] == 0 and s['snf_failures'] == 0
        raw = os.path.join(EVIDENCE, s['raw'])
        if not os.path.exists(raw):
            ok = False
            continue
        lines = open(raw).read().splitlines()
        ok &= sum(l.startswith('DONE') for l in lines) == s['groups']
        ok &= sum(l.startswith('HIT') for l in lines) == s['hits']
        ok &= not any(l.startswith(('MISMATCH', 'BELOW')) for l in lines)
    for t in ev.get('atlas', []):
        ok &= t['unexpected_hits'] == 0
    return {'pass': bool(ok), 'scans': len(ev['scans'])}


def main():
    results = {
        'SO3_PROPOSITION': gate_so3(),
        'PRIMITIVE_SL3': gate_primitive(),
        'SCAN_SMALL': gate_scan(),
        'ATLAS_SMALL': gate_atlas(),
        'EVIDENCE_SUMMARY': gate_evidence(),
    }
    allp = all(v['pass'] for v in results.values())
    for k, v in results.items():
        print(k, 'PASS' if v['pass'] else 'FAIL', '' if v['pass'] else v.get('reason', ''))
    if '--write' in sys.argv:
        with open(os.path.join(EVIDENCE, 'check_mckay_minimal.json'), 'w') as fh:
            json.dump({'schema': 'cbmd.mckay-minimal.check.v1', 'gates': results, 'pass': allp}, fh, indent=1)
            fh.write('\n')
    print('ALL PASS' if allp else 'FAILURES')
    return 0 if allp else 1


if __name__ == '__main__':
    sys.exit(main())
