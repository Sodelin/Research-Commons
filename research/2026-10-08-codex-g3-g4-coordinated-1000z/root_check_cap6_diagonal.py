"""Independent exact Fraction interval six-root diagonal on the cap-five cube.

Only the literal rational source input is used. No numerical forest producer,
source module, compiler or target search is executed. Original independent
current-root routing gives the stated symmetric bare-cell no-merger formula.
"""
from fractions import Fraction as F
from hashlib import sha256
from math import comb
from pathlib import Path
import json
import sys

class I:
    def __init__(self,a,b=None):
        self.a,self.b=F(a),F(a if b is None else b)
        assert self.a<=self.b
    def __add__(self,y):
        y=lift(y);return I(self.a+y.a,self.b+y.b)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a)
    def __sub__(self,y):return self+-lift(y)
    def __rsub__(self,y):return lift(y)+-self
    def __mul__(self,y):
        y=lift(y);v=[a*b for a in (self.a,self.b) for b in (y.a,y.b)]
        return I(min(v),max(v))
    __rmul__=__mul__
    def __truediv__(self,y):
        y=lift(y);assert not y.a<=0<=y.b
        return self*I(1/y.b,1/y.a)
    def __pow__(self,n):
        assert isinstance(n,int) and n>=0
        out=I(1)
        for _ in range(n):out=out*self
        return out

def lift(x):return x if isinstance(x,I) else I(x)
def enc(x):
    # Exact outward rational grid avoids enormous unreduced-display integers.
    scale=10**100
    low,high=F((x.a*scale)//1,scale),F(-((-x.b*scale)//1),scale)
    assert low<=x.a<=x.b<=high
    return [str(low),str(high)]

def main(input_path,output):
    raw=input_path.read_bytes()
    assert sha256(raw).hexdigest()=='bb6bcc498125a86b797748f8f936b60051ac327f07d761fab2caeab531d70a8e'
    doc=json.loads(raw);fixed=doc['fixed_rational_source']
    t,d=F(fixed['t']),F(fixed['d']);r=F(doc['parameter_cube_radius'])
    A=list(map(F,fixed['means']))
    weights=[I(F(x)-r,F(x)+r) for x in doc['approximate_rational_parameters'][:3]]+[I(fixed['w4'])]
    normalized=I(1);cells=[]
    for aa,w in zip(A,weights):
        st=1-aa*t;h2=w*t**3;p6=I(0)
        for k in range(7):
            px,py=comb(k,2),comb(6-k,2)
            lo,diff=min(px,py),abs(px-py)
            symmetric=(I(st*st)-h2)**lo*sum((comb(diff,2*j)*st**(diff-2*j)*h2**j for j in range(diff//2+1)),I(0))
            p6+=F(comb(6,k),64)*symmetric
        q=1-aa*t/2
        normalized=normalized*(p6/q**15)**2
        cells.append({'p6':enc(p6),'pair_survival':str(q)})
    difference=d**15*(normalized-I(1))
    assert difference.b<0
    result={'status':'PASS','input_sha256':sha256(raw).hexdigest(),
            'script_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
            'method':'Exact rational interval polynomial evaluation of independent fair bare-cell no-merger diagonals; eight shared cells and exact pair telescoping.',
            'cube_radius':str(r),'pair_target':str(d),'cell_bounds':cells,
            'output_endpoint_encoding':'Exact rational outward grid 10^-100; internal arithmetic uses unrounded Fraction intervals.',
            'preserved_attempt_limitation':'Initial serialization exceeded Python integer-display digit limit after the negative-sign check passed; outward rational grid fixes representation only.',
            'normalized_six_root_diagonal':enc(normalized),'b6_minus_target_exact_rational_interval':enc(difference),
            'b6_minus_target_approximate_interval':[format(float(difference.a),'.16e'),format(float(difference.b),'.16e')],
            'strictly_negative_over_entire_cube':True,'implicit_exact_cap5_center_covered':True,
            'full_six_root_forest_checked':False,'all_cap_or_G4_obstruction':False}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','difference_approximate':result['b6_minus_target_approximate_interval'],'full_six_root_forest_checked':False}))

if __name__=='__main__':main(Path(sys.argv[1]),Path(sys.argv[2]))
