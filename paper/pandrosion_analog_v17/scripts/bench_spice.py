from pathlib import Path
import subprocess,tempfile,time,json,statistics,random,shutil
import numpy as np
P=Path(__file__).resolve().parents[1];ng=shutil.which('ngspice') or '/opt/homebrew/bin/ngspice'
rows=[];order=['ad','halley']*7;random.Random(1709).shuffle(order)
for mode in order:
 with tempfile.TemporaryDirectory()as t:
  q=Path(t);(q/'core.cir').write_text((P/f'analog_p4/{mode}_buffered.cir').read_text())
  start=time.perf_counter();pr=subprocess.run([ng,'-b','core.cir'],cwd=q,capture_output=True,text=True,timeout=60);dt=time.perf_counter()-start
  assert pr.returncode==0
  a=np.loadtxt(q/'waveform.txt',skiprows=1);assert np.isfinite(a).all()
  v=float(np.interp(645e-6,a[:,0],a[:,11]));err=v/(4.096*2**(1/3))-1;assert abs(err)<3e-5
  rows.append(dict(mode=mode,wall_seconds=dt,output_error=err))
(P/'data/spice_wall.json').write_text(json.dumps(dict(runs=rows,summary={m:dict(median_seconds=statistics.median(x['wall_seconds']for x in rows if x['mode']==m),min_seconds=min(x['wall_seconds']for x in rows if x['mode']==m),max_seconds=max(x['wall_seconds']for x in rows if x['mode']==m))for m in ['ad','halley']},scope='Process launch + transient solve + wrdata output; not device latency',simulated_seconds=.00065),indent=2)+'\n')
print('14 SPICE timing runs checked')
