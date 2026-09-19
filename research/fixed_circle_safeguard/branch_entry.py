"""Branch-driven circle/AD protocol: availability replaces the residual gate.

The whole-branch contraction theorem justifies every regular circle readout.
AD is used outside the real branch or at excluded charts. The old halving gate
remains available in model.py as an independently certified alternative.
"""
from model import Diagram

class BranchEntryDiagram(Diagram):
    def step(self,force_reject=False):
        before=self.count.copy();t=self.value(self.tpoint)
        if t==1:return {'kind':'exact','cost':{k:0 for k in before}}
        trial,reason=self.candidate()
        # Test-only extra rejection exercises the complete fallback cost.
        if trial is None or force_reject:
            self.state=self.fallback();kind='AD'
        else:
            self.state=trial;kind='circle'
        self.E,self.tpoint=self.power_residual(self.state)
        self.s=self.value(self.state)
        return {'kind':kind,'reason':reason,'t_before':t,'t_after':self.value(self.tpoint),
                'cost':{k:self.count[k]-before[k] for k in before}}

def branch_costs(p):
    m=p.bit_length()-1+p.bit_count()-1
    return {'m':m,'initial':{'J':5*m+2,'P':0,'C':0},
            'circle':{'J':5*m+8,'P':0,'C':0},
            'fallback_after_trial':{'J':5*m+10,'P':2,'C':1}}
