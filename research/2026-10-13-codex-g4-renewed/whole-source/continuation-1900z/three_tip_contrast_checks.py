"""Finite exact controls for the three-tip gauge hand proof, not a proof."""
from pathlib import Path
from fractions import Fraction as Q
from math import comb, prod
import hashlib, json, sys

ROOT = Path(__file__).resolve().parents[4]
UPSTREAM = ROOT / 'research/2026-10-01-g4-admitted-testers-0819z'
sys.path.insert(0, str(UPSTREAM))
from forest_algebra import edge_law, forest, graft, relabel, tree, death_polynomial

def kappa(k):
    return Q(1, prod(comb(j, 2) for j in range(2, k+1)))

def death(k, r, z):
    return sum(c*z**e for e,c in death_polynomial(k,r).items())

def caterpillar(m, j):
    t=tree(0, 2)
    for b in range(3,j+2): t=tree(t,b)
    t=tree(t,1)
    for b in range(j+2,m+2): t=tree(t,b)
    return t

def split_law(m, z):
    out={}
    for early in [0,1]:
        labels=[early]+list(range(2,m+2))
        for f,p in edge_law(m+1,z).items():
            moved=forest([relabel(t,dict(enumerate(labels))) for t in f]+[1-early])
            for tail,q in edge_law(len(moved),Q(0)).items():
                t=graft(moved,tail)[0]
                out[t]=out.get(t,Q(0))+p*q
    return out

def formula(m,j,z):
    value=2*z**comb(m+1,2)*kappa(m+2)
    for r in range(1,j+1):
        den=prod(comb(ell,2) for ell in range(m+2-r,m+2))
        value+=death(m+1,m+1-r,z)*kappa(m+2-r)/den
    return value

rows=[]
for z in [Q(1,3),Q(2,5),Q(4,5)]:
    for m in [2,3]:
        direct=split_law(m,z)
        for j in range(1,m+1):
            actual=direct[caterpillar(m,j)]
            expected=formula(m,j,z)
            assert actual==expected
            if j>=2:
                delta=actual-direct[caterpillar(m,j-1)]
                assert delta==kappa(m+1)*death(m+1,m+1-j,z)/comb(m+2-j,2)
            rows.append({'m':m,'j':j,'z':str(z),'probability':str(actual)})

# Recover all parameters from the exact normalized table at two controls.
for g,x0,x1,z in [(Q(2,5),Q(2,3),Q(3,5),Q(4,7)),
                  (Q(1,2),Q(1),Q(1),Q(1,3))]:
    q=1-g
    v2=(g*g*x0+q*q*x1)/3+g*q*(1-z/3)
    R={}
    for m in [2,3]:
        for j in range(1,m+1):
            R[m,j]=((g*g*x0+q*q*x1*z**comb(m,2))*kappa(m+2)
                    +g*q*formula(m,j,z))/(v2*kappa(m+1)*(g+q*z**comb(m,2)))
    assert (R[3,3]-R[3,2])/(R[3,2]-R[3,1])==3*death(4,1,z)/death(4,2,z)
    d={m:(R[m,m]-R[m,m-1])/death(m+1,1,z) for m in [2,3]}
    k=d[2]/d[3]
    r=(1-k)/(k*z-z**3)
    recovered_g=1/(1+r)
    recovered_v2=recovered_g*(1-recovered_g)/(d[2]*(recovered_g+(1-recovered_g)*z))
    assert recovered_g==g and recovered_v2==v2
    c={m:(R[m,1]*v2*kappa(m+1)*(g+q*z**comb(m,2))-g*q*formula(m,1,z))/kappa(m+2)
       for m in [2,3]}
    recovered_x1=(c[2]-c[3])/(q*q*(z-z**3))
    recovered_x0=(c[2]-q*q*recovered_x1*z)/(g*g)
    assert recovered_x0==x0 and recovered_x1==x1

result={'status':'passed exact finite controls','split_probability_checks':len(rows),
        'parameter_recovery_controls':2,'arithmetic':'fractions.Fraction',
        'scope':'Finite algebra/forest checks only; no general source proof or Lean verification.',
        'upstream_sha256':hashlib.sha256((UPSTREAM/'forest_algebra.py').read_bytes()).hexdigest(),
        'rows':rows}
Path(__file__).with_name('three-tip-contrast-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
