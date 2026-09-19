"""Remove improvements one at a time; no root used for electrical calibration."""
from pathlib import Path
import json
from model import prepare
from spice import run
from revised_circuit import prepare_revision,calibrate_memory

def main():
 r=prepare([[3,.037]])[0];cfg,_=prepare_revision(3,85,1,20264000)
 variants={'complete':cfg,'one_conversion':{**cfg,'output_average_count':1},
  'no_adc_trim':{**cfg,'adc_calibration':None},
  'no_cell_trim':{**cfg,'read_compensation':None,'stage_compensation':None,'target_calibration':None}}
 without_current={**cfg,'leak_compensation_A':0.}
 memory,_=calibrate_memory(without_current,20264004)
 variants['no_leak_compensation']={**without_current,'memory_calibration':memory}
 rows=[]
 for name,c in variants.items():
  result=run(r,step='1u',config=c);rows.append(dict(variant=name,**result))
  print(name,result['configured_adc_relative_error'],flush=True)
 Path(__file__).with_name('revised_ablation.json').write_text(json.dumps(dict(scope='One held-out hot low-degree case, diagnostic ablation only',runs=rows),indent=2)+'\n')
if __name__=='__main__':main()
