"""Independent 100-digit check of certificates emitted by the browser preparation."""
import json
import subprocess
import mpmath as mp
mp.mp.dps=100
js="""
import {initializeCalibrated} from './docs/initialization.js';
const rows=[];
for(const band of ['compact','wide'])for(const p of [3,17,1024,65536,1000000])for(const X of [Number.MIN_VALUE,1e-200,.1,1,2,500000,1e200,Number.MAX_VALUE]){
 const r=initializeCalibrated(p,X,band);rows.push({p,X,band,c:r.c,Y:r.X,lo:r.enclosure.lo.toString(),hi:r.enclosure.hi.toString(),e:r.enclosure.e});
}
console.log(JSON.stringify(rows));
"""
rows=json.loads(subprocess.check_output(['node','--input-type=module','-e',js],text=True))
for row in rows:
    p=row['p']
    actual=mp.mpf(float(row['X']))*mp.mpf(float(row['c']))**p
    lo=mp.mpf(row['lo'])*mp.power(2,row['e'])
    hi=mp.mpf(row['hi'])*mp.power(2,row['e'])
    assert lo<=actual<=hi,(row,actual,lo,hi)
    assert (mp.mpf('.25')<=actual<=4 if row['band']=='wide' else 1<=actual<=2)
    assert abs(actual-mp.mpf(float(row['Y'])))<=mp.power(2,-48)
print(json.dumps({'status':'PASS','independent_certificates':len(rows),'precision_digits':mp.mp.dps}))
