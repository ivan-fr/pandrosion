from pathlib import Path
import json
P=Path(__file__).resolve().parents[1]
b=json.loads((P/'data/benchmark.json').read_text())
s='\\begin{table}[htbp]\\centering\\small\n\\caption{Median microseconds per solve on '+b['metadata']['cpu']+', Python '+b['metadata']['python']+', mpmath '+b['metadata']['mpmath']+'. Nine batches of 100 solves; full round timings are archived.}\\label{tab:digital}\n\\begin{tabular}{@{}rrrrr@{}}\\toprule\n$p$ & Newton & Halley & AD inverse & \\texttt{mpmath.root}\\\\\\midrule\n'
for p in [3,4,8,16,32]:
 vals=[next(x['median_us']for x in b['rows']if x['p']==p and x['method']==m) for m in ['Newton','Halley','AD inverse','mpmath.root']]
 s+=str(p)+' & '+' & '.join(f'{v:.2f}'for v in vals)+'\\\\\n'
s+='\\bottomrule\\end{tabular}\\end{table}\n'
(P/'data/digital_table.tex').write_text(s)
w=json.loads((P/'data/spice_wall.json').read_text())
s='\\begin{table}[htbp]\\centering\\small\n\\caption{ngspice 46 process wall time for a 650\\,$\\mu$s simulated trace, $m=2$. Seven runs per netlist. These seconds are host computation time.}\\label{tab:spicetime}\n\\begin{tabular}{@{}lrrr@{}}\\toprule\nNetlist & Median (s) & Minimum (s) & Maximum (s)\\\\\\midrule\n'
for k,label in [('ad','Buffered AD'),('halley','Buffered Halley')]:
 z=w['summary'][k];s+=label+' & '+' & '.join(f'{z[x]:.3f}'for x in ['median_seconds','min_seconds','max_seconds'])+'\\\\\n'
s+='\\bottomrule\\end{tabular}\\end{table}\n';(P/'data/spice_table.tex').write_text(s)
