"""compare.py A B: two versions on the 50 000 polynomials.  Expects the outputs of the runner in o-A-1,
o-A-2, o-B-1, o-B-2 (two runs of each version, one file out_<family>.txt per family): the time of a
polynomial is the smaller of its two times (microseconds below), and the discs are compared by their
multiplicities and counts, with the flags `complete` and `within_tolerance`."""
import sys, statistics
F=['real_gauss','complex_gauss','small_int','kac_pm1','wide_scale','integer_roots_mult','gaussian_roots_mult','real_cluster']
def load(v,f):
    runs=[[l.split() for l in open(f'o-{v}-{i}/out_{f}.txt')] for i in (1,2)]
    t=[min(int(a[2]),int(b[2]))/1e3 for a,b in zip(*runs)]
    shape=[(a[0],a[1],sorted(zip(a[9::5],a[10::5]))) for a in runs[0]]
    ex=sum(int(a[4])>0 for a in runs[0])
    return t,shape,ex
A,B=sys.argv[1],sys.argv[2]; ta=tb=0
print(f"{'family':20s} {'n':>6s} {'beyond':>6s} | {A+' med':>10s} {'p99':>7s} {'total s':>8s} | {B+' med':>10s} {'p99':>7s} {'total s':>8s} | ratio  discs differ")
for f in F:
    a,sa,ea=load(A,f); b,sb,eb=load(B,f); ta+=sum(a); tb+=sum(b)
    q=lambda t:sorted(t)[int(.99*len(t))]
    print(f"{f:20s} {len(a):6d} {eb:6d} | {statistics.median(a):10.1f} {q(a):7.0f} {sum(a)/1e6:8.3f} | {statistics.median(b):10.1f} {q(b):7.0f} {sum(b)/1e6:8.3f} | {sum(a)/sum(b):5.2f}  {sum(x!=y for x,y in zip(sa,sb))}")
print(f"total {ta/1e6:.3f} s -> {tb/1e6:.3f} s, ratio {ta/tb:.2f}")
