"""Independent limiting-case check of the authored closed-loop amplifier stage."""
import tempfile,subprocess,json
from pathlib import Path
import numpy as np
from simulate_p2 import deck,NG,P
net,_=deck('AD',1)
sub=net[net.index('.subckt OA'):net.index('.ends OA')+len('.ends OA')]
rows=[]
for voltage in [2.,5.]:
 s=f'''Calibration stage check
Vraw raw 0 {voltage}
Vtrim trim 0 0.5
Rin raw sum1 10k
Rf neg sum1 10.1k
Ri trim sum1 1meg
X1 0 sum1 neg OA
Rin2 neg sum2 10k
Rf2 corrected sum2 10k
X2 0 sum2 corrected OA
Rl corrected 0 10k
Cl corrected 0 20p
{sub}
.control
set wr_singlescale
set wr_vecnames
tran 100n 100u 0 100n uic
wrdata test.txt v(corrected)
quit
.endc
.end
'''
 with tempfile.TemporaryDirectory() as t:
  p=Path(t);(p/'test.cir').write_text(s)
  r=subprocess.run([NG,'-b','test.cir'],cwd=p,capture_output=True,text=True,timeout=30)
  assert r.returncode==0,r.stderr
  a=np.loadtxt(p/'test.txt',skiprows=1)
 expected=1.01*voltage+.0101*.5
 actual=float(a[-1,1]);assert abs(actual-expected)<50e-6,(actual,expected)
 rows.append(dict(input=voltage,expected=expected,actual=actual,error_volts=actual-expected))
(P/'stage_validation.json').write_text(json.dumps(rows,indent=2)+'\n')
print(rows)
