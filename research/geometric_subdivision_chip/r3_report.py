"""Tables and figure for R3 from the campaign JSON files (no simulation)."""
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent; OUT = HERE / 'r3'
ppm = lambda x: None if x is None else x * 1e6
fmt = lambda x, d=4: '—' if x is None else f'{x:.{d}g}'

def main():
    val = json.loads((OUT / 'root_accuracy.json').read_text())['rows']
    stress = json.loads((OUT / 'stress.json').read_text())
    steps = json.loads((OUT / 'transitions.json').read_text())
    start = json.loads((OUT / 'startup.json').read_text()) if (OUT / 'startup.json').exists() else None
    noise = json.loads((OUT / 'noise.json').read_text()) if (OUT / 'noise.json').exists() else None
    err = lambda r: r['r3']['result'].get('window_error')
    # figure: R2 vs R3 on every pair with an R2 value
    fig, ax = plt.subplots(1, 2, figsize=(12, 5), layout='constrained')
    for split, c, m in [('development', '#555555', 's'), ('r2_heldout', '#2b6cb0', 'o'), ('fresh', '#247a58', '^')]:
        rs = [r for r in val if r['split'] == split and r.get('r2_window_error') and err(r)]
        ax[0].scatter([r['r2_window_error'] * 1e6 for r in rs], [err(r) * 1e6 for r in rs], c=c, marker=m, s=40,
                      label={'development': 'développement', 'r2_heldout': 'validation R2 (24)', 'fresh': 'nouveau jeu (28)'}[split])
    ax[0].plot([1e-3, 1e5], [1e-3, 1e5], '--', color='gray'); ax[0].set(xscale='log', yscale='log', xlim=(1e-2, 3e4), ylim=(1e-3, 3e4),
        xlabel='R2 : erreur relative (ppm)', ylabel='R3 : erreur relative (ppm)', title='Même couple (p, X), départ de zéro pour R3')
    ax[0].legend(loc='upper left', fontsize=9)
    labels, fr, rc = [], [], []
    for s in stress:
        if s['p'] != 3.7: continue
        labels.append(', '.join(f'{k}={v}' for k, v in s['variation'].items() if k != 'seed') + (f' #{s["variation"]["seed"]}' if 'seed' in s['variation'] else ''))
        fr.append(s['frozen']['result'].get('window_error') or np.nan); rc.append(s['recalibrated']['result'].get('window_error') or np.nan)
    y = np.arange(len(labels))
    ax[1].barh(y + .2, np.array(fr) * 1e6, .4, color='#c5443b', label='trims gelés à 25 °C')
    ax[1].barh(y - .2, np.array(rc) * 1e6, .4, color='#247a58', label='procédure refaite dans la condition')
    ax[1].set(yticks=y, yticklabels=labels, xscale='log', xlabel='erreur relative (ppm)', title='p = 3,7, X = 2 : perturbations')
    ax[1].legend(fontsize=9); fig.savefig(OUT / 'validation.png', dpi=150); plt.close(fig)
    # tables
    t = ['# Mesures R3', '', 'Erreur relative maximale sur les 20 derniers % d\'une simulation de 20 µs démarrant de zéro (R3) ; R1/R2 : valeurs de leur propre campagne (point DC, 2 µs). Pour le nouveau jeu, R2 est rejoué ici avec sa procédure inchangée.', '',
         '| Groupe | p | X | R1 (ppm) | R2 (ppm) | R3 (ppm) | R3 : excès racine−1 | R3 : 1 ppm atteint à (µs) | Vu pendant la conception |', '|---|---:|---:|---:|---:|---:|---:|---:|---|']
    for r in val:
        res = r['r3']['result']; st = (res.get('settle_time_s') or {}).get('1e-06')
        t.append(f"| {r['split']} | {r['p']:.9g} | {r['X']:g} | {fmt(ppm(r.get('r1_window_error')))} | {fmt(ppm(r.get('r2_window_error')))} | {fmt(ppm(err(r)))} | "
                 f"{fmt(res.get('excess_error'), 3)} | {fmt(None if st is None else st * 1e6, 3)} | {'oui' if r.get('seen_during_design') else ''} |")
    t += ['', '## Perturbations (sans / avec réétalonnage dans la condition)', '', '| p | X | Condition | Trims gelés (ppm) | Procédure refaite (ppm) |', '|---:|---:|---|---:|---:|']
    for s in stress:
        t.append(f"| {s['p']:.9g} | {s['X']:g} | {s['variation']} | {fmt(ppm(s['frozen']['result'].get('window_error')))} | {fmt(ppm(s['recalibrated']['result'].get('window_error')))} |")
    t += ['', '## Échelons d\'entrée (même exposant binaire)', '', '| p | X avant → après | pas (ns) | Erreur finale (ppm) | 100 / 10 / 1 ppm après l\'échelon (µs) |', '|---:|---|---:|---:|---|']
    for s in steps:
        a = s['result'].get('settle_after_step_s') or {}
        t.append(f"| {s['p']:.9g} | {s['X1']:g} → {s['X2']:g} | {s['dt']*1e9:g} | {fmt(ppm(s['result'].get('window_error')))} | "
                 + ' / '.join(fmt(None if a.get(k) is None else a[k] * 1e6, 3) for k in ('0.0001', '1e-05', '1e-06')) + ' |')
    if start:
        t += ['', '## Démarrage', '', f"Départ brutal (rails et sources à t=0, tensions nulles) : {start['summary']['hard_start_settled']}/{start['summary']['hard_start_total']} établis ; "
              f"rampe d'alimentation 1 µs : {start['summary']['ramp_settled']}/{start['summary']['ramp_total']}. Détail dans [startup.json](startup.json).", '']
    if noise:
        t += ['', '## Bruit petit signal', '', '| p | X | 1 Hz–1 kHz | 1 Hz–1 MHz | 1 Hz–1 GHz | Moyennage pour 10 / 1 ppm RMS |', '|---:|---:|---:|---:|---:|---|']
        for n in noise:
            b = [f"{x['relative_RMS']*1e6:.4g} ppm" for x in n['bands']]; a = n['averaging_time_s_for']
            t.append(f"| {n['p']:g} | {n['X']:g} | {b[0]} | {b[1]} | {b[2]} | {a['10ppm']*1e3:.3g} ms / {a['1ppm']:.3g} s |")
    (OUT / 'MEASUREMENTS.md').write_text('\n'.join(t) + '\n')

if __name__ == '__main__': main()
