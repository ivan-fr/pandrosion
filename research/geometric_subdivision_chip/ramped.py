"""Startup with finite supply/reference ramps, separate from the fixed campaign."""
import json
import campaign as C
if __name__=='__main__':
 for p,X in [(3.7,2),(1e6,500000)]:
  C.run(f'ramp_{p}',kind='root',p=p,X=X,n=6,ramp=True,duration=5e-6)
 (C.ROOT/'results/ramped.json').write_text(json.dumps(C.rows,indent=2)+'\n')
