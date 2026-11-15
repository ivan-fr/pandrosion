"""Variants of the sweep in the same Rust code.  Run after rust_check.py (which writes the data files)."""
import subprocess
BIN = 'pandroots/target/release/bench'
def t(path, mode, reps=25):
    out = subprocess.run([BIN, path, str(reps), mode], capture_output=True, text=True, check=True).stdout.split()
    d = {out[i]: out[i + 1] for i in range(0, len(out), 2)}
    return float(d['time_us']), float(d['sweeps']), d['isolated_complete'] == d['polys']
modes = [('aberth', 'AK, nothing announced (Ehrlich-Aberth)'), ('ak-ak', 'AK, neighbours announced by AK'), ('ak-three', 'AK, announced by three means'), ('three-ak', 'three means, announced by AK'), ('g8', 'three means twice (G8)'), ('jacobi', 'G8 without Gauss-Seidel'), ('circle', 'G8 from one circle')]
print('microseconds per polynomial (mean sweeps), best of 4 x 25 runs; * = not all certified')
print('kind deg | ' + ' | '.join(n for _, n in modes))
for kind in ('complex', 'real'):
    for deg in (5, 10, 20, 40, 80, 160, 320):
        path = 'data/%s_%d.txt' % (kind, deg); line = []
        for mode, _ in modes:
            r = [t(path, mode) for _ in range(4)]; b = min(r)
            line.append('%.1f (%.2f)%s' % (b[0], b[1], '' if all(x[2] for x in r) else '*'))
        print('%-7s %3d | ' % (kind, deg) + ' | '.join(line), flush=True)
