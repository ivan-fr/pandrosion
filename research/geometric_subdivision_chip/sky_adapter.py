"""Auditable research adapter of pinned SkyWater models. Not signoff/PDK validation."""
from pathlib import Path
import re
P=Path(__file__).parent/'vendor/sky130'
def models(corner='t'):
 # Nominal process random variables = zero in official montecarlo parameters.
 params=dict(dkispp5x=1.00460,dkbfpp5x=1.12880,dkisepp5x=.745,dknfpp5x=1.0009)
 s='\n'.join(p.read_text() for p in P.glob('*.model.spice'))
 caps={'diode_pw2dn__ajunction_mult':.982,'diode_ps2dn__pjunction_mult':1.01160,'nfet_01v8__ajunction_mult':.99543,'diode_ps2nw__ajunction_mult':.98286,'diode_ps2nw__pjunction_mult':.98954,'pfet_01v8__ajunction_mult':.99626,'pfet_01v8__pjunction_mult':1.00090}
 for name in set(re.findall(r'sky130\w+junction_mult',s)):
  params[name]=next(v for k,v in caps.items() if name.endswith(k))
 result=['* PNP nominal; selected NPN corner only. Continuous BJT area is an adapter assumption.','.param mult=1 area=1']
 result += ['.param '+k+'='+str(v) for k,v in params.items()]
 result += [l for l in (P/f'sky130_fd_pr__npn_05v5__{corner}.corner.spice').read_text().splitlines() if not l.startswith('.include')]
 for p in sorted(P.glob('*.model.spice')):
  for line in p.read_text().splitlines():
   if line.startswith(('.subckt','.ends','qsky')) or line.strip()=='+':continue
   if line.startswith('.model '):line=line.replace(line.split()[1], 'QN' if 'npn_' in p.name else 'QP',1)
   result.append(line)
 return result
