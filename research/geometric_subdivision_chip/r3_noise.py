"""R3 small-signal noise around the operating point reached by the zero-start transient.
The DC solver does not converge on its own for the R3 netlists; the final transient state is given as
.nodeset (a convergence hint only; the operating point is still solved by ngspice).
Output noise is integrated over three bands and converted to a relative RMS error of the output current.
Generic BJT models contain shot and thermal noise, no flicker noise (KF=0): low-frequency noise is optimistic.
"""
import json, re, subprocess, sys
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import r3, r3_calibrate as C

OUT = HERE / 'r3'

def run(p, X, cfg, gain, tag):
    d = OUT / 'raw' / f'noise_{tag}'; d.mkdir(parents=True, exist_ok=True)
    lines, sense, meta = r3.build(kind='root', p=p, X=X, n=6, output_gain=gain, **C.BASE, **cfg)
    src = '\n'.join(lines) + '\n'
    (d / 'tran.cir').write_text(src + '.control\nset filetype=ascii\ntran 5n 20u uic\nwrite final.raw\n.endc\n.end\n')
    subprocess.run([r3.NG, '-b', 'tran.cir'], cwd=d, capture_output=True, timeout=900)
    hdr, data = (d / 'final.raw').read_text().split('Values:\n')
    names = [l.split()[1] for l in hdr.split('Variables:\n')[1].strip().splitlines()]; nv = len(names); vals = data.split()
    pts = len(vals) // (nv + 1); last = vals[(pts - 1) * (nv + 1) + 1:pts * (nv + 1)]
    nodeset = '.nodeset ' + ' '.join(f'v({n[2:-1]})={float(x):.12g}' for n, x in zip(names, last) if n.startswith('v(') and n[2:-1] not in ('vcc', 'vee'))
    src = re.sub(r'^(Iunit vcc n_unit \S+)$', r'\1 ac 1', src, flags=re.M)
    bands = [(1, 1e3), (1, 1e6), (1, 1e9)]
    ctrl = ['.control', 'set noaskquit', 'op', 'print i(Vmeas)'] + [c for f0, f1 in bands for c in (f'noise v(n_load) Iunit dec 10 {f0:g} {f1:g}', 'print onoise_total')] + ['.endc', '.end']
    (d / 'noise.cir').write_text(src + nodeset + '\n' + '\n'.join(ctrl) + '\n')
    o = subprocess.run([r3.NG, '-b', 'noise.cir'], cwd=d, capture_output=True, text=True, timeout=900).stdout
    (d / 'ngspice.log').write_text(o)
    iout = float(re.search(r'i\(vmeas\) = (\S+)', o).group(1)); tot = [float(x) for x in re.findall(r'onoise_total = (\S+)', o)]
    vout = abs(iout) * 1000.   # 1 kOhm load
    return dict(p=p, X=X, output_V=vout, bands=[dict(band_Hz=b, noise_V_RMS=n, relative_RMS=n / vout) for b, n in zip(bands, tot)],
                white_density_relative_per_sqrtHz=tot[1] / vout / (1e6 - 1) ** .5)

if __name__ == '__main__':
    cal = json.loads((OUT / 'calibration.json').read_text())['config']
    val = json.loads((OUT / 'root_accuracy.json').read_text())['rows']
    rows = []
    for p, X in [(3.7, 2.), (1e6, 5e5)]:
        g = next(r['r3']['output_gain'] for r in val if r['p'] == p and r['X'] == X)
        rows.append(run(p, X, cal, g, f'{p:g}_{X:g}')); print(rows[-1], flush=True)
    for r in rows:   # averaging time for a given RMS level, assuming the white density (optimistic: no flicker)
        r['averaging_time_s_for'] = {f'{ppm}ppm': (r['white_density_relative_per_sqrtHz'] / (ppm * 1e-6)) ** 2 / 2 for ppm in (100, 10, 1)}
    (OUT / 'noise.json').write_text(json.dumps(rows, indent=1) + '\n')
