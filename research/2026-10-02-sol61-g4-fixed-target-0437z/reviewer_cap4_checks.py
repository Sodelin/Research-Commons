#!/usr/bin/env python3
"""Independent exact symbolic cap-four source checks.
Reviewer: GPT-6.1 Sol / review_fixed_target_replica, 2026-10-02.
Uses the inherited ASTRA forest compiler; no numerical search or root solve.
"""
from fractions import Fraction as Q
import hashlib, json, sys
from pathlib import Path
import sympy as S
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'g4-allcopy-2237z'))
import forest_algebra as F

def size(t):
    return 1 if isinstance(t,int) else size(t[0])+size(t[1])
def orbit(f):
    if len(f)==4:return 'singletons'
    if len(f)==3:return 'pair'
    if len(f)==2:return 'cherries' if all(size(t)==2 for t in f) else 'triple'
    return 'balanced' if size(f[0][0])==2 else 'caterpillar'
def representation(alg, tup):
    q,r,s,c,h=tup
    p3=2*(r-s)
    p1=1-S.Rational(9,5)*q+r-s/5+S.Rational(3,10)*c
    p2=1-p1-p3-s
    totals={'singletons':s,'pair':p3,'triple':S.Rational(2,3)*p2-c,
            'cherries':p2/3+c,'balanced':p1/3+h,'caterpillar':S.Rational(2,3)*p1-h}
    counts={'singletons':1,'pair':6,'triple':12,'cherries':3,'balanced':3,'caterpillar':12}
    ans=[]
    for n,f in alg.coords:
        if n<=1:ans.append(S.Integer(1))
        elif n==2:ans.append(q if len(f)==2 else 1-q)
        elif n==3:
            ans.append(r if len(f)==3 else (q-r)/2 if len(f)==2 else (1-S.Rational(3,2)*q+r/2)/3)
        else:ans.append(totals[orbit(f)]/counts[orbit(f)])
    return tuple(ans)
def compose(K,L):
    q,r,s,c,h=K;Q_,R,T,C,H=L
    return (q*Q_,r*R,s*T,Q_*c+s*C,h+(1-Q_)*c+s*H)

alg=F.ForestAlgebra(4)
q,r,s,c,h,Q_,R,T,C,H=S.symbols('q r s c h Q R S C H')
k=(q,r,s,c,h);ell=(Q_,R,T,C,H)
actual=alg.mul(representation(alg,k),representation(alg,ell))
expected=representation(alg,compose(k,ell))
assert all(S.expand(a-b)==0 for a,b in zip(actual,expected))
print('PASS generic 48-coordinate graft composition',flush=True)
# Source polynomials are compiled by actual current-root coin assignments and
# finite Kingman jump/death laws, retaining every labelled output forest.
x,y,g,z=S.symbols('x y g z')
polys=alg.cell_polynomials('independent')
bare=tuple(sum(S.Rational(v.numerator,v.denominator)*x**ex*y**ey*g**eg
              for (ex,ey,eg,ez),v in p.items()) for p in polys)
def coord(n,f):return bare[alg.index[n,f]]
bs=[coord(n,tuple(range(n))) for n in (2,3,4)]
p1=sum(v for (n,f),v in zip(alg.coords,bare) if n==4 and len(f)==1)
p2=sum(v for (n,f),v in zip(alg.coords,bare) if n==4 and len(f)==2)
two=sum(v for (n,f),v in zip(alg.coords,bare) if n==4 and orbit(f)=='cherries')
bal=sum(v for (n,f),v in zip(alg.coords,bare) if n==4 and orbit(f)=='balanced')
A=g*(1-x);B=(1-g)*(1-y)
compactC=S.Rational(2,3)*((1-g)*A**3+g*B**3-3*g*(1-g)*(A-B)**2)
assert S.expand(two-p2/3-compactC)==0
assert S.expand(bal-p1/3)==0
expected=representation(alg,(*bs,compactC,0))
assert all(S.expand(a-b)==0 for a,b in zip(bare,expected))
print('PASS genuine bare C/H and all 48 source coordinates',flush=True)
receipt={
 'status':'PASS', 'scope':'exact symbolic identities only; inherited compiler, not independent compiler',
 'generic_graft_composition_coordinates':len(actual),
 'genuine_bare_source_coordinates':len(bare),
 'bare_C_from_two_cherry_total':'PASS', 'bare_H_from_balanced_total':'PASS',
 'compiler_sha256':hashlib.sha256(Path(F.__file__).read_bytes()).hexdigest(),
 'reviewer_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'sympy':S.__version__
}
Path(__file__).with_name('reviewer-cap4-checks.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
