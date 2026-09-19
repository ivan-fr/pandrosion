import {initializeCalibrated} from '../../docs/initialization.js';
const inputs=process.argv[2]?JSON.parse(process.argv[2]):[[1000000,500000]];
console.log(JSON.stringify(inputs.map(([p,X])=>{
 const r=initializeCalibrated(p,X,'compact');
 return {p,originalX:X,c:r.c,Y:r.X,comparisons:r.comparisons,precision:r.precision,calibrationErrorBound:r.calibrationErrorBound};
})));
