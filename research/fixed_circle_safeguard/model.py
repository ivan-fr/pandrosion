"""Guarded fixed-circle/AD geometry. High precision, no root used for decisions.

Every moving point is computed by line/parallel/circle intersection. The exact
scalar formulas are used only by the validation program. Preparation, incidence
classification and order comparisons are recorded separately from mobile traces.
"""
from pathlib import Path
import importlib.util
import mpmath as mp

ROOT=Path(__file__).resolve().parents[2]
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,ROOT/path)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
base=module('sg_base','paper/reciprocal_geometry_v20/src/decentered/verify.py')
circle=module('sg_circle','paper/reciprocal_geometry_v20/src/fixed_circle/verify.py')

class Diagram:
    W=mp.mpf(2);H=mp.mpf(4)
    def __init__(self,p,X,s,record=False):
        self.p=p;self.X=mp.mpf(X);self.s=mp.mpf(s);self.record=record
        self.count={'J':0,'P':0,'C':0,'comparisons':0,'identity_checks':0};self.lines=[]
        self.O=(0,self.H);self.A=(self.W,self.H);self.B=(self.W,0);self.C=(0,0)
        self.left=base.join(self.C,self.O);self.right=base.join(self.B,self.A)
        self.top=base.join(self.O,self.A);self.horizontal=base.join(self.C,self.B)
        self.M=(0,self.H*(1-1/self.X))
        self.ADcenter=(self.W-2*self.W/(p-1),self.H-self.H*(p+1)/(self.X*(p-1)))
        self.ADvertical=base.join(self.ADcenter,(self.ADcenter[0],self.ADcenter[1]+1))
        self.rho,self.h,self.j,self.zx,self.zy,self.k=circle.parameters(p)
        self.Z=(self.zx,self.zy);self.center=(self.h,self.j)
        assert self.rho!=1 and self.k>0
        self.radius2=(self.W-self.h)**2+self.j**2
        self.state=self.R(self.s)
        self.E,self.tpoint=self.power_residual(self.state)
        self.initial_count=self.count.copy()
    def R(self,q):return (self.W,self.H*(1-q))
    def value(self,P):return 1-P[1]/self.H
    def J(self,a,b):
        self.count['J']+=1
        if self.record:self.lines.append(('J',a,b))
        return base.join(a,b)
    def P(self,line,point):
        self.count['P']+=1
        if self.record:self.lines.append(('P',line,point))
        return base.parallel(line,point)
    def left_project(self,f,P):return base.cross(self.J(self.hub(f),P),self.left)
    def right_project(self,f,P):return base.cross(self.J(self.hub(f),P),self.right)
    def scale(self,c,P):
        f=c/(2*(1+c));g=1/(2*(1+c))
        return self.right_project(g,self.left_project(f,P))
    def mul(self,a,b):
        self.count['identity_checks']+=1
        if b==self.B:return a
        V=base.cross(self.J(self.C,b),self.top)
        L=self.left_project(mp.mpf('0.5'),a)
        Q=base.cross(self.J(V,L),self.right)
        return self.right_project(mp.mpf('0.25'),self.left_project(mp.mpf('0.5'),Q))
    def power(self,s):
        acc=s
        for bit in bin(self.p)[3:]:
            acc=self.mul(acc,acc)
            if bit=='1':acc=self.mul(s,acc)
        return acc
    def power_residual(self,s):
        E=self.power(s)
        return E,self.scale(self.X,E)
    def hub(self,f):return (self.W*f/(f-1),self.H)
    def candidate(self):
        # Uniform binary input avoids the old CP center at infinity when s=1.
        T=self.scale(self.k,self.tpoint)
        L=base.cross(self.J(self.hub(self.rho),self.state),self.left)
        line=self.J(self.Z,T)
        dx=T[0]-self.Z[0];dy=T[1]-self.Z[1]
        ox=self.Z[0]-self.h;oy=self.Z[1]-self.j
        aa=dx*dx+dy*dy;bb=2*(dx*ox+dy*oy);cc=ox*ox+oy*oy-self.radius2
        disc=bb*bb-4*aa*cc
        if disc<=0:return None,'no transverse crossing'
        choices=[]
        for sign in [-1,1]:
            lam=(-bb+sign*mp.sqrt(disc))/(2*aa)
            G=(self.Z[0]+lam*dx,self.Z[1]+lam*dy)
            gx=G[0]-self.B[0];gy=G[1]-self.B[1]
            den=self.W*gy+self.H*gx
            if den==0:continue
            # Label of the premarked descending arc, not an extra moving join.
            v=self.H*self.rho*gx/den
            if v>0 and (self.p**2-4)*(v*v+1)-2*(self.p**2+2)*v<0:
                choices.append((G,v))
        if len(choices)!=1:return None,'branch unavailable'
        G,v=choices[0]
        # Conservative numerical chart rejection. The exact construction tests
        # zero; finite precision rejects an additional small neighborhood. The
        # global proof allows arbitrary extra rejections and still applies.
        tol=mp.sqrt(mp.eps)
        if (mp.hypot(G[0]-self.B[0],G[1]-self.B[1])<=tol*(1+mp.sqrt(self.radius2))
            or abs(v-self.rho)<=tol*(1+abs(v))):
            return None,'readout chart singular'
        try:
            U=base.cross(self.J(self.B,G),self.top)
            out=base.cross(self.J(U,L),self.right)
        except AssertionError:return None,'readout chart singular'
        if self.value(out)<=0:return None,'nonpositive candidate'
        return out,'candidate'
    def gate(self,candidate):
        E,u=self.power_residual(candidate)
        square=self.mul(u,u)
        product=self.mul(self.tpoint,square)
        # Values on one rail: larger q means lower ordinate. Three comparisons.
        self.count['comparisons']+=3
        t_le_one=self.tpoint[1]>=0
        if t_le_one:
            cmp2=square[1]<=self.tpoint[1];cmp3=product[1]>=0
        else:
            cmp2=self.tpoint[1]<=square[1];cmp3=product[1]<=0
        accepted=cmp2 and cmp3
        return accepted,E,u,square,product
    def fallback(self):
        self.count['C']+=1
        radius=abs(self.A[1]-self.E[1])
        # Lower intersection of the circle with its center's prepared vertical.
        D=(self.ADcenter[0],self.ADcenter[1]-radius)
        green=self.J(self.M,self.E);support=self.J(self.A,D)
        T=base.cross(self.P(green,self.state),support)
        return base.cross(self.P(self.horizontal,T),self.right)
    def step(self,force_reject=False):
        before=self.count.copy();t=self.value(self.tpoint)
        if t==1:return {'kind':'exact','cost':{k:0 for k in before}}
        trial,reason=self.candidate();accepted=False
        if trial is not None:
            accepted,E,u,square,product=self.gate(trial)
            if force_reject:accepted=False
        if accepted:
            self.state,self.E,self.tpoint=trial,E,u;kind='circle'
        else:
            self.state=self.fallback()
            self.E,self.tpoint=self.power_residual(self.state);kind='AD'
        self.s=self.value(self.state)
        return {'kind':kind,'reason':reason,'t_before':t,'t_after':self.value(self.tpoint),
                'cost':{k:self.count[k]-before[k] for k in before}}

def costs(p):
    L=p.bit_length()-1;m=L+p.bit_count()-1
    return {'L':L,'m':m,
      'initial':{'J':5*m+2,'P':0,'C':0},
      'accepted':{'J':5*m+18,'P':0,'C':0},
      'rejected_after_trial':{'J':10*m+22,'P':2,'C':1}}
