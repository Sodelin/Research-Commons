"""Independent piecewise-density integration controls; never reads biological data."""
import hashlib,json,time
from fractions import Fraction as F
from pathlib import Path
import certified_forward as f

class ExpPoly:
    """Exact finite sum c_a exp(-a) at rational fixture parameters."""
    def __init__(self,terms):self.terms={F(a):F(c) for a,c in terms.items() if c}
    @staticmethod
    def cast(x):return x if isinstance(x,ExpPoly) else ExpPoly({F(0):F(x)})
    @staticmethod
    def E(a):return ExpPoly({F(a):F(1)})
    def __add__(self,x):
        d=dict(self.terms)
        for a,c in self.cast(x).terms.items():d[a]=d.get(a,F(0))+c
        return ExpPoly(d)
    __radd__=__add__
    def __neg__(self):return ExpPoly({a:-c for a,c in self.terms.items()})
    def __sub__(self,x):return self+-self.cast(x)
    def __rsub__(self,x):return self.cast(x)+-self
    def __mul__(self,x):
        d={}
        for a,c in self.terms.items():
            for b,e in self.cast(x).terms.items():d[a+b]=d.get(a+b,F(0))+c*e
        return ExpPoly(d)
    __rmul__=__mul__
    def enclosed(self,bits):
        result=f.Interval.point(0)
        for a,c in self.terms.items():result+=c*f.exp_neg(a,bits)
        return result

def density_pieces(p):
    """Literal intervals of the accepted six pair densities; BB C path stays split."""
    h,t1,t0,g=(p[k] for k in ('h','t1','t0','g'));a,b,c,d,r=(p[k] for k in ('rA','rB','rC','rAB','rR'));u=t1-h;v=t0-t1;E=ExpPoly.E;s=E(b*h)
    return {
      'AC':[(t0,None,1,r)],
      'AB':[(t1,t0,1-g,d),(t0,None,g+(1-g)*E(d*v),r)],
      'BC':[(h,t0,g,c),(t0,None,1-g+g*E(c*(t0-h)),r)],
      'AA':[(0,t1,1,a),(t1,t0,E(a*t1),d),(t0,None,E(a*t1+d*v),r)],
      'CC':[(0,t0,1,c),(t0,None,E(c*t0),r)],
      'BB':[(0,h,1,b),(h,t1,s*(1-g)**2,b),(h,t1,s*g*g,c),(t1,t0,s*(1-g)**2*E(b*u),d),(t1,t0,s*g*g*E(c*u),c),(t0,None,s*((1-g)**2*E(b*u+d*v)+g*g*E(c*(t0-h))+2*g*(1-g)),r)]
    }

def integrate_pieces(p,z):
    ans={}
    for pair,rows in density_pieces(p).items():
        total=ExpPoly.cast(0)
        for start,end,weight,rate in rows:
            value=ExpPoly.E(z*start)
            if end is not None:value-=ExpPoly.E(z*end+rate*(end-start))
            total+=weight*(rate/(rate+z))*value
        ans[pair]=total
    return ans

FIXTURES={
 'distinct_rates':dict(h='1/16',t1='1/8',t0='3/16',g='1/3',rA=1,rB=2,rC=3,rAB=4,rR=5),
 'equal_rates':dict(h='1/16',t1='1/8',t0='3/16',g='1/3',rA=2,rB=2,rC=2,rAB=2,rR=2)
}

def main():
    start=time.monotonic();reports={};identities=0;checks=0;normalizations=0
    for name,params in FIXTURES.items():
        p,m,means=f.evaluate(params,64)
        for k in range(56):
            z=F(8*k,3);grouped=f.pair_expressions(p,z,ExpPoly.E);pieces=integrate_pieces(p,z)
            for pair in f.PAIRS:
                if grouped[pair].terms!=pieces[pair].terms:raise AssertionError('density integral mismatch')
                identities+=1
                if k==0:
                    if pieces[pair].terms!={F(0):F(1)}:raise AssertionError('normalization failure')
                    normalizations+=1
                else:
                    if not m[pair][k-1].intersects(pieces[pair].enclosed(100)):raise AssertionError('interval/density mismatch')
                    checks+=1
        if name=='equal_rates':
            for k in range(1,56):
                value=F(2)/(F(2)+F(8*k,3))
                for pair in ('AA','CC'):
                    if not m[pair][k-1].contains(value):raise AssertionError('equal-rate reduction')
        for pair in f.PAIRS:
            if not all(m[pair][k].lo>m[pair][k+1].hi for k in range(54)):raise AssertionError('fixture monotonicity not certified')
        reports[name]=f.report(params,64)
        if time.monotonic()-start>180:raise f.ResourceBound('control wall budget exceeded')
    b=Path(__file__).resolve().parent
    return {'schema':'certified-pair-laplace-controls-v1','source_sha256':hashlib.sha256((b/'certified_forward.py').read_bytes()).hexdigest(),'control_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'exact_grouped_vs_piecewise_exponential_polynomial_identities':identities,'exact_zero_moment_normalizations':normalizations,'independent_piecewise_interval_comparisons':checks,'mean_enclosures_per_fixture':330,'all_feature_widths_at_most':'1/18446744073709551616','equal_rate_AA_CC_exact_rational_reductions':110,'strict_moment_monotonicity_certified_on_fixtures':True,'fixtures':reports,'no_estimation_or_inverse_search':True,'no_data_fit_or_MCMC':True,'not_formal_verification':True}
if __name__=='__main__':print(json.dumps(main(),indent=2))
