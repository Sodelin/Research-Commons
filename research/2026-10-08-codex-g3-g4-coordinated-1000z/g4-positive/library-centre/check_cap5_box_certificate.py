"""Exact rational audit of saved interval bounds and contraction inclusion.

This consumer independently checks bound arithmetic, strict source domains
and pinned producer identities. It does not independently derive the forest
Jacobian; replay the pinned producer or review its interval AD for that step.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import json


class I:
    def __init__(self,a,b=None):
        self.a,self.b=F(a),F(a if b is None else b)
        assert self.a<=self.b
    def __add__(self,y):
        y=lift(y);return I(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self): return I(-self.b,-self.a)
    def __sub__(self,y): return self+-lift(y)
    def __rsub__(self,y): return lift(y)+-self
    def __mul__(self,y):
        y=lift(y);v=[a*b for a in [self.a,self.b] for b in [y.a,y.b]]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,y):
        y=lift(y);assert not y.a<=0<=y.b
        return self*I(1/y.b,1/y.a)
    def __rtruediv__(self,y):return lift(y)/self
    def absolute(self):
        return I(0 if self.a<=0<=self.b else min(abs(self.a),abs(self.b)),max(abs(self.a),abs(self.b)))
    def contains(self,y): return self.a<=y.a and y.b<=self.b


def lift(y):return y if isinstance(y,I) else I(y)
def pair(q):return I(*q)


def verify(root,input_path,cert_path):
    raw=input_path.read_bytes();doc=json.loads(raw);cert=json.loads(cert_path.read_text())
    assert cert['status']=='EXECUTED_OUTWARD_INTERVAL_CONTRACTION_GATE_PASS'
    assert cert['input_sha256']==sha256(raw).hexdigest()
    base=Path(__file__).resolve().parent
    assert cert['own_source_sha256']==sha256((base/'certify_cap5_box.py').read_bytes()).hexdigest()
    assert cert['helper_sha256']==sha256((root/'research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-forest/exact_forest_layer.py').read_bytes()).hexdigest()
    assert cert['original_source_sha256']==sha256((root/'research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py').read_bytes()).hexdigest()
    r=F(doc['parameter_cube_radius']);assert r>0 and cert['parameter_cube_radius']==str(r)
    C=[[F(x) for x in row] for row in cert['explicit_rational_preconditioner_C']]
    J=[[pair(x) for x in row] for row in cert['complete_Jacobian_interval_on_cube']]
    Fc=[pair(x) for x in cert['center_F_interval']]
    assert len(C)==len(J)==len(Fc)==8 and all(len(row)==8 for row in C+J)
    E=[[I(int(i==j))-sum((C[i][k]*J[k][j] for k in range(8)),I(0)) for j in range(8)] for i in range(8)]
    for i,row in enumerate(E):
        for j,v in enumerate(row):assert pair(cert['identity_minus_CJ_interval'][i][j]).contains(v)
    q=max(sum(v.absolute().b for v in row) for row in E)
    assert q<=F(cert['contraction_infinity_norm_upper_bound_exact_rational'])<F(1,2)
    CF=[sum((C[i][j]*Fc[j] for j in range(8)),I(0)) for i in range(8)]
    s=max(v.absolute().b for v in CF)
    assert s<=F(cert['center_displacement_infinity_upper_bound_exact_rational'])<r/4
    M=F(cert['M_conservative_exact_rational']);assert M>=max([F(1)]+[sum(abs(c) for c in row) for row in C])
    eta=F(cert['certified_target_scaled_coordinate_radius_exact_rational'])
    assert eta==r/(4*M) and q*r+s+M*eta<r
    fixed=doc['fixed_rational_source'];AA=list(map(F,fixed['means']));t=F(fixed['t'])
    assert AA[0]>0 and min(AA)>0 and fixed['d']=='1/4' and F(fixed['a'])*F(fixed['b'])==F(fixed['d'])
    w=[I(F(x)-r,F(x)+r) for x in doc['approximate_rational_parameters'][:3]]+[I(fixed['w4'])]
    for i,(A,W) in enumerate(zip(AA,w)):
        st=I(1-A*t);hh=W*t**3
        ref=[W,st,hh,st*st-hh,I((A*t)**2)-hh]
        for j,v in enumerate(ref):
            bound=pair(cert['arm_strictness_gate_intervals'][i][j]);assert bound.contains(v) and bound.a>0
        assert pair(cert['arm_strictness_gate_intervals'][i][1]).b<1
    theta=[I(F(x)-r,F(x)+r) for x in doc['approximate_rational_parameters'][3:]]
    X1,X2,X3,X6,X7=theta
    a,b,U,seam=map(F,[fixed[k] for k in ['a','b','U','seam']])
    qq=[1-A*t/2 for A in AA];assert min(qq)>0
    X4,X5=qq[0]*seam/b,1/(b*seam)
    edges=[I(a*b*U/qq[2]),X7/(qq[1]*U),X6/(qq[3]*X7),I(X5)/(qq[0]*X6),I(seam),
           I(seam),X3/(qq[3]*X4),X2/(qq[1]*X3),X1/(qq[2]*X2),1/X1]
    for got,ref in zip(cert['ordinary_edge_interval_bounds_exact_rational'],edges):
        bound=pair(got);assert bound.contains(ref) and 0<bound.a<=bound.b<1
    leading=I(a*b*U/qq[2])*I(1-r,1+r)
    bound=pair(cert['ninth_leading_edge_interval_exact_rational']);assert bound.contains(leading) and 0<bound.a<=bound.b<1
    return {'status':'EXACT_RATIONAL_BOUND_AND_DOMAIN_AUDIT_PASS','q_less_than_one_half':True,'source_cube_strict':True,
            'target_inclusion_exact':True,'parameter_cube_radius':str(r),'target_radius':str(eta),
            'limits':'Saved forest Jacobian derivation still relies on pinned outward interval producer and independent source review.'}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parents[4])
    ap.add_argument('--input',type=Path,required=True);ap.add_argument('--certificate',type=Path,required=True)
    args=ap.parse_args();print(json.dumps(verify(args.root,args.input,args.certificate),indent=2))


if __name__=='__main__':main()
