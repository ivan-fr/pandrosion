"""Two-point OFFLINE readout calibration; distinct held-out SPICE inputs.
No calibration amplifier is claimed to have been built or included in the netlist.
"""
import json
from pathlib import Path
from simulate_p1 import simulate
P=Path(__file__).parent

def main():
 data=json.loads((P/'results.json').read_text());rows=[]
 for mode in ['AD','Halley']:
  for profile in ['trimmed_stress','untrimmed_stress']:
   base={x['m']:x for x in data['nominal_grid']if x['mode']==mode and x['profile']==profile}
   y0=base[1.]['samples'][-1]['output'];y1=base[2.]['samples'][-1]['output']
   a=(2**(1/3)-1)/(y1-y0);b=1-a*y0
   tests=[]
   for m in [1.1,1.35,1.6,1.9]:
    raw=simulate(mode,m,profile);y=raw['samples'][-1]['output'];err=(a*y+b)/m**(1/3)-1
    tests.append({'m':m,'raw_error':raw['final_error'],'corrected_error':err,'clip_ratio':raw['peak_port_ratio_after_reset']})
   rows.append({'mode':mode,'profile':profile,'gain':a,'offset_normalized':b,'calibration_inputs':[1,2],'held_out':tests})
 print('16 independent held-out SPICE runs complete.')
 out={'status':'completed','scope':'Offline affine correction fitted at m=1,2; fixed gains applied to held-out points. Physical correction stage, gain/offset drift and temperature not modeled.','results':rows,'additional_spice_runs':16}
 (P/'calibration.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':main()
