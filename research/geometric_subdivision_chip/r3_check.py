"""R3 audit: protocol order, calibration provenance, oracle-free core netlists, standalone ngspice replays,
SHA-256 manifest. It checks bookkeeping and reproducibility; it does not turn a failed case into a success."""
import hashlib, json, re, shutil, subprocess, sys
from pathlib import Path
import numpy as np
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r3, r3_calibrate as C

OUT = HERE / 'r3'
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    cal = json.loads((OUT / 'calibration.json').read_text()); val = json.loads((OUT / 'root_accuracy.json').read_text())
    frozen = hashlib.sha256(json.dumps(cal['config'], sort_keys=True).encode()).hexdigest()
    assert frozen == cal['sha256'] == val['config_sha256'], 'validation did not use the frozen calibration'
    # calibration code: no root/power/log evaluation of the job input
    src = (HERE / 'r3_calibrate.py').read_text()
    forbidden = [w for w in ('mpmath', 'mp.power', 'math.pow', 'math.log(X', '** (1 /', '**(1/', 'reference=str') if w in src]
    assert not forbidden, forbidden
    assert all(abs(A * B - t * t) < 1e-15 for A, B, t in C.IDENT), 'identities must be exact: mean(u^2, v^2) = u v'
    # core netlist: transistors, resistors, capacitors, clamp diodes, ideal I (inputs/bias/bleed/trims), V (rails, 0 V senses)
    kinds = {}
    for p, X in [(3.7, 2.), (1e6, 5e5)]:
        lines, _, meta = r3.build(kind='root', p=p, X=X, n=6, **C.BASE, **cal['config'])
        body = [l for l in lines[1:] if l and not l.startswith(('.', '*'))]
        bad = [l for l in body if l[0] not in 'QRCDIV']
        assert not bad, bad[:3]
        vs = [l for l in body if l[0] == 'V' and not l.split()[0] in ('Vcc', 'Vee')]
        assert all(l.split()[3] == '0' for l in vs), 'only 0 V sense sources besides the two rails'
        isrc = [l.split()[0] for l in body if l[0] == 'I']
        cls = lambda n: 'input DAC' if re.match(r'I(unit|x|a|b|cal_a|cal_b)$', n) else n.split('_')[0][1:]
        k = {}
        for n in isrc: k[cls(n)] = k.get(cls(n), 0) + 1
        kinds[f'{p:g}/{X:g}'] = dict(transistors=meta['transistors'], resistors=sum(l[0] == 'R' for l in body), capacitors=sum(l[0] == 'C' for l in body),
                                    clamp_diodes=sum(l[0] == 'D' for l in body), ideal_current_sources=k)
    # standalone replays of three validation netlists
    rows = {(r['split'], r['p'], r['X']): r for r in val['rows']}
    picks = [('development', 3.7, 2.), ('development', 1e6, 5e5), ('fresh', 5.5, 777.)]
    replays = []
    for split, p, X in picks:
        r = rows[(split, p, X)]['r3']['result']
        src = OUT / 'raw' / f'val_{p:.12g}_{X:.12g}' / 'run'
        dst = OUT / 'examples' / f'{split}_{p:g}_{X:g}'; dst.mkdir(parents=True, exist_ok=True)
        shutil.copy(src / 'circuit.cir', dst / 'circuit.cir')
        pr = subprocess.run([r3.NG, '-b', 'circuit.cir'], cwd=dst, capture_output=True, text=True, timeout=900)
        (dst / 'ngspice.log').write_text(pr.stdout + pr.stderr)
        d = np.loadtxt(dst / 'trace.txt', skiprows=1); final = d[-1, 1] / r['I0'] * r['scale']
        replays.append(dict(case=f'{split} p={p:g} X={X:g}', netlist_sha256=sha(dst / 'circuit.cir'), trace_sha256=sha(dst / 'trace.txt'),
                            campaign_final=r['final'], replay_final=float(final), absolute_difference=float(abs(final - r['final']))))
        assert abs(final - r['final']) < 1e-9, replays[-1]
    files = sorted([p for p in OUT.glob('*') if p.is_file() and p.name not in ('SHA256SUMS',)] + list((OUT / 'examples').rglob('*.cir')) + list((OUT / 'examples').rglob('trace.txt'))
                   + [HERE / f for f in ('r3.py', 'r3_calibrate.py', 'r3_campaign.py', 'r3_noise.py', 'r3_check.py', 'r3_report.py', 'r3_startup.py')])
    result = dict(frozen_config_sha256=frozen, calibration_written_before_scoring=cal.get('written_before_scoring'), identities=C.IDENT,
                  forbidden_tokens_in_calibration=forbidden, netlists=kinds, standalone_replays=replays,
                  behavioral_sources_in_core=False, note='Ideal elements: two rails, 0 V senses, input DAC currents, bias/bleed/trim currents.')
    (OUT / 'VALIDATION.json').write_text(json.dumps(result, indent=1) + '\n')
    (OUT / 'SHA256SUMS').write_text(''.join(f'{sha(f)}  {f.relative_to(HERE)}\n' for f in files if f.exists()))
    print(json.dumps(result, indent=1))

if __name__ == '__main__': main()
