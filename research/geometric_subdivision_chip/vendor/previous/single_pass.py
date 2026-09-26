"""Single-pass (memoryless) version of the V30 centered binary-power AD chain, any p in 3..10^6.

Identical to output/github/pandrosion-v23/research/analog_fast_ad/spice.py in every cell expression,
error term, guard and converter model, except:
  * no state capacitor, no next-state capacitor, no switches, no reset, no clock: the state input of
    the read cell is a programmed DAC voltage q0 (coefficient-quantized), and the AD correction is
    applied once;
  * q0 is either 0 (the V30 start) or the digitally evaluated first AD step
    q0 = p (C_p(Y) - 1), C_p(Y) = (p+1+(p-1)Y)/(p-1+(p+1)Y): rational arithmetic, no root oracle;
  * a job is a simultaneous step of the DAC (q0) and of the programmed Y at t0, from the trivial
    preceding job (Y=1, q0=0); the readout is the candidate node after settling, converted by the
    same ADC transfer model, decoded by 1/[c(1+q/p)];
  * leakage, charge injection and switch parameters have no counterpart and are ignored;
  * the stage time constant tau (10 ohm x stage capacitor) is a study parameter; tau = 1 us
    reproduces the V30 filters; noise knots and edges scale with tau.
"""
import json, shutil, subprocess, tempfile
from pathlib import Path
import numpy as np, mpmath as mp
from v30_bridge import prepare, schedule, decode, config, calibrate, calibrate_adc, spice_timeout
P = Path(__file__).parent
NG = shutil.which('ngspice') or '/opt/homebrew/bin/ngspice'
COUNT = 0

def seed_q0(kind, p, Y):
    if kind == 'zero':
        return 0.0
    if kind == 'ad1':
        return p * ((p + 1 + (p - 1) * Y) / (p - 1 + (p + 1) * Y) - 1)
    raise ValueError(kind)

def deck(p, Y, q0, cfg, tau=1e-6, prev=(1.0, 0.0), step_div=20):
    offset, gain, rin = cfg['offset'], cfg['gain'], cfg['rin']
    cf = (lambda x: round(x * 2 ** cfg['coeff_bits']) / 2 ** cfg['coeff_bits']) if cfg.get('coeff_bits') else (lambda x: x)
    Yq, invp, q0q = cf(Y), cf(1 / p), cf(q0); Yp, q0p = cf(prev[0]), cf(prev[1])
    ts = tau / 1e-6; t0 = 2 * tau; edge = 10e-9 * ts; ops = schedule(p); N = len(ops)
    duration = t0 + max(4 * (N + 4) + 20, 220) * tau; C = tau / 10   # >= 220 tau so that a 16-sample average spaced 10 tau fits
    L = [f'Single-pass centered AD chain p={p}', '.options reltol=1e-7 abstol=1e-12 vntol=1e-9',
         f'Vdac dac 0 PULSE({q0p:.17g} {q0q:.17g} {t0:.17g} {edge:.17g} {edge:.17g} 1 2)',
         f'Vy y 0 PULSE({Yp:.17g} {Yq:.17g} {t0:.17g} {edge:.17g} {edge:.17g} 1 2)']
    if cfg.get('noise_rms'):
        rng = np.random.default_rng(cfg['noise_seed'])
        for node in ['readnoise', 'targetnoise']:
            n = round(duration / (10e-6 * ts)) + 1
            knots = ' '.join(f'{t:.17g} {v:.17g}' for t, v in zip(np.linspace(0, duration, n), rng.normal(0, cfg['noise_rms'], n)))
            L.append(f'V{node} {node} 0 PWL({knots})')
    def stage(name, expr):
        L.extend([f'B{name} {name}_drive 0 V=min(2,max(-2,({expr})))', f'R{name} {name}_drive {name} 10',
                  f'C{name} {name} 0 {C:.17g}', f'Rport_{name} {name} 0 {rin}', f'Cport_{name} {name} 0 2p'])
    readexpr = f'v(dac)+{offset}' + ('+v(readnoise)' if cfg.get('noise_rms') else '')
    if cfg.get('read_compensation'):
        a, b = cfg['read_compensation']; readexpr += f'+({a:.17g})+({b:.17g})*v(dac)'
    stage('q', readexpr); prev_n = 'q'
    for i, op in enumerate(ops):
        name = f'd{i}'; w = cf(op['product_weight'])
        if op['kind'] == 'square':
            expr = f'v({prev_n})+{w:.17g}*((1+{gain})*v({prev_n})*v({prev_n})+{offset})+{offset}'
        else:
            expr = f'v({prev_n})+{cf(op["copy_weight"]):.17g}*(v(q)-v({prev_n}))+{w:.17g}*((1+{gain})*v({prev_n})*v(q)+{offset})+{offset}'
        if cfg.get('stage_compensation'):
            a, b, c, d, e = cfg['stage_compensation'][i]
            expr += f'+({a:.17g})+({b:.17g})*v({prev_n})+({c:.17g})*v(q)+({d:.17g})*v({prev_n})*v({prev_n})+({e:.17g})*v({prev_n})*v(q)'
        stage(name, expr); prev_n = name
    peak = 'abs(v(q_drive))'
    for i in range(N): peak = f'max({peak},abs(v(d{i}_drive)))'
    L.append(f'Bpeak stagepeak 0 V={peak}')
    target = f'(v(q)+2*(1+v(q)*{invp:.17g})*(1-v(residual))/max(0.25,v(denominator)))*(1+{cfg["target_gain"]})+{cfg["target_offset"]}' + ('+v(targetnoise)' if cfg.get('noise_rms') else '')
    if cfg.get('target_calibration'):
        a, b = cfg['target_calibration']; target = f'(({target})-({a:.17g}))/({b:.17g})'
    L += [f'Bres residual 0 V=v(y)*(1+v({prev_n}))', f'Bden denominator 0 V=1+v(residual)+(v(residual)-1)*{invp:.17g}',
          f'Btarget target 0 V={target}', 'Bcandidate candidate_drive 0 V=min(2,max(-2,v(target)))',
          'Rcandidate candidate_drive candidate 10', f'Ccandidate candidate 0 {C:.17g}',
          '.control', 'set noaskquit', 'set numdgt=16', 'set wr_singlescale', 'set wr_vecnames',
          f'tran {tau/step_div:.17g} {duration:.17g} 0 {tau/step_div:.17g}',
          'wrdata wave.txt v(candidate) v(q) v(residual) v(denominator) v(target) v(stagepeak)', 'quit', '.endc', '.end']
    return '\n'.join(L) + '\n', dict(t0=t0, duration=duration, stages=N, q0=q0q, Y=Yq)

def convert(values, cfg):
    """V30 ADC transfer model, vectorized (spice.run.convert)."""
    lsb = 4 / 2 ** cfg.get('adc_bits', 18); inl = cfg.get('adc_inl_lsb', 0) * lsb
    if cfg.get('adc_inl_period_V', 0): inl = inl * np.sin(2 * np.pi * values / cfg['adc_inl_period_V'])
    observed = values * (1 + cfg.get('adc_gain', 0)) + cfg.get('adc_offset', 0) + inl
    assert np.all(np.abs(observed) < 2), 'Configured ADC input outside the modeled range'
    result = np.round(observed / lsb) * lsb
    if cfg.get('adc_calibration'):
        a, b = cfg['adc_calibration']; result = (result - a) / b
    return result

def run(case, seed_kind, cfg, tau=1e-6, keep=None, prev=(1.0, 0.0), step_div=20, targets=(1e-4, 1e-5, 1e-6, 1e-7)):
    global COUNT
    p, Y, c = case['p'], case['Y'], case['c']; q0 = seed_q0(seed_kind, p, Y)
    text, meta = deck(p, Y, q0, cfg, tau, prev, step_div)
    with tempfile.TemporaryDirectory(prefix='pandro_p6_') as d:
        (Path(d) / 'x.cir').write_text(text)
        pr = subprocess.run([NG, '-b', 'x.cir'], cwd=d, capture_output=True, text=True, timeout=max(spice_timeout(), 600))
        if pr.returncode: raise RuntimeError((pr.stdout + pr.stderr)[-3000:])
        a = np.loadtxt(Path(d) / 'wave.txt', skiprows=1)
        if keep:
            (P / f'{keep}.cir').write_text(text); (P / f'{keep}.log').write_text(pr.stdout + pr.stderr)
            np.savetxt(P / f'{keep}.csv', a[::10], delimiter=',', header='time,candidate,q,residual,denominator,target,stagepeak', comments='')
    COUNT += 1
    t = a[:, 0]; q = a[:, 1]; sel = t >= meta['t0']
    mp.mp.dps = 80; ref = mp.exp(mp.log(mp.mpf(case['originalX'])) / p)
    # uniform grids by interpolation (ngspice points are non-uniform): tau/4 for settling, tau for the stored trajectory
    tt = t[sel] - meta['t0']; qraw_i = q[sel]
    g4 = np.arange(0, tt[-1], tau / 4); q4 = np.interp(g4, tt, qraw_i); qc4 = convert(q4, cfg)
    err = np.array([float(mp.mpf(decode(c, float(v), p)) / ref - 1) for v in qc4]); err = np.abs(err)
    settle = {}
    for tol in targets:
        bad = np.where(err > tol)[0]
        settle[f'{tol:g}'] = None if len(bad) == 0 else (float(g4[bad[-1] + 1]) if bad[-1] + 1 < len(g4) else None)
    qc = convert(qraw_i, cfg)
    final_q = float(qc[-1]); final_err = float(abs(mp.mpf(decode(c, final_q, p)) / ref - 1))
    qsettle = {}
    for tolv in (1e-5, 1e-6, 1e-7):
        bad = np.where(np.abs(q4 - q4[-1]) > tolv)[0]
        qsettle[f'{tolv:g}'] = None if len(bad) == 0 else float(g4[bad[-1]])
    g1 = np.arange(0, tt[-1], tau); traj_t = g1.tolist(); traj_q = convert(np.interp(g1, tt, qraw_i), cfg).tolist()
    initial_err = float(abs(mp.mpf(decode(c, float(convert(np.array([meta['q0']]), cfg)[0]), p)) / ref - 1))
    res = dict(p=p, X=case['originalX'], seed=seed_kind, q0=meta['q0'], stages=meta['stages'], tau_s=tau, duration_s=meta['duration'],
               initial_error=initial_err, final_error=final_err, final_q=final_q, raw_final_q=float(q[-1]),
               settling_s=settle, state_settling_s=qsettle, trajectory=dict(t=traj_t, q=traj_q),
               stage_peak=float(a[:, 6].max()), denominator_min=float(a[sel, 4].min()), target_peak=float(np.abs(a[:, 5]).max()))
    assert res['denominator_min'] > .25 and res['target_peak'] < 2 and res['stage_peak'] < 1.99, 'Guard/clamp activated: cannot claim normal operation'
    return res
