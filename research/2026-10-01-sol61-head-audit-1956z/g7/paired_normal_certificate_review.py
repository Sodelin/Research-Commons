"""Independent rational certificate review, with no log-sign sampling.
Rechecks saved polynomial identities and global loss-budget constants.
"""
import json,math,hashlib,platform
from fractions import Fraction as F
from pathlib import Path
from argparse import ArgumentParser
from collections import defaultdict

def mul(a,b):
    out=defaultdict(F)
    for i,x in a.items():
        for j,y in b.items():out[i+j]+=x*y
    return {i:x for i,x in out.items() if x}
def ev(a,x):return sum((v*x**i for i,v in a.items()),F(0))
def sub(a,b):
    out=defaultdict(F,a)
    for i,v in b.items():out[i]-=v
    return {i:v for i,v in out.items() if v}
def divroot(a,r):
    out={};rem=dict(a)
    for k in range(max(a),0,-1):
        v=rem.get(k,F(0));out[k-1]=v;rem[k]=F(0);rem[k-1]=rem.get(k-1,F(0))+r*v
    assert rem.get(0,F(0))==0
    return {i:v for i,v in out.items() if v}

def main():
    ap=ArgumentParser();ap.add_argument('--certificate',required=True);args=ap.parse_args()
    path=Path(args.certificate);d=json.loads(path.read_text());normal={};shift_terms={}
    for tag,nodes in [('F0',[F(1,2)]),('F1',[F(1,2),F(1,4)])]:
        z=d[tag];la=z['exponents'];c=list(map(F,z['covector']))
        assert sum(c)==1 and sum(x*l for x,l in zip(c,la))==0
        poly={0:F(1),**{l:-x for x,l in zip(c,la)}}
        factors={0:F(1)}
        for a,b in [(F(1),F(-1))]+[(F(2),F(-1)) if r==F(1,2) else (F(4),F(-1)) for r in nodes]:
            factors=mul(factors,mul({1:a,0:b},{1:a,0:b}))
        cs=list(map(F,z['positive_quotient_coefficients']));assert all(x>0 for x in cs)
        quotient={len(cs)-1-i:x for i,x in enumerate(cs)}
        assert mul(factors,quotient)==poly
        B=sum(abs(x) for x in c);k=-sum(x*l*l for x,l in zip(c,la));assert k>0
        assert B==F(z['absolute_covector_sum']) and k==F(z['negative_second_power_sum'])
        # Re-expand the SAVED normalized numerator at q=1-y using independent
        # exact binomial arithmetic, including endpoint p=0 and p=1.
        shifted=defaultdict(F)
        for term in z['normalized_second_q_derivative_numerator']:
            ip,iq,co=term['p_power'],term['q_power'],F(term['coefficient'])
            for iy in range(iq+1):shifted[ip,iy]+=co*math.comb(iq,iy)*(-1)**iy
        shifted={ij:x for ij,x in shifted.items() if x}
        assert shifted.get((0,0))==k
        assert all(iy>0 or (ip==0 and co==k) for (ip,iy),co in shifted.items())
        tail=sum(abs(co) for (ip,iy),co in shifted.items() if iy>0)
        assert tail==F(z['q1_shifted_coefficient_norm'])
        gap=F(z['q1_gap']);assert 0<gap<=F(1,4) and gap*tail<=k/2
        shift_terms[tag]=len(shifted);normal[tag]=(poly,B,gap)
    f1,B1,gap1=normal['F1'];_,B0,gap0=normal['F0'];r=F(1,2)
    f2=sub({i:2*v for i,v in f1.items()},{2*i:v for i,v in f1.items()})
    f2q=divroot(divroot(f2,r),r);B2=sum(abs(v) for v in f2q.values())
    f3=sub(sub({i:3*v for i,v in f1.items()},{2*i:3*v for i,v in f1.items()}),{3*i:-v for i,v in f1.items()})
    M3=sum(abs(i*v) for i,v in f3.items());f3r=ev(f3,r)
    assert f3r==ev(f1,r**3)>0
    c={k:F(v) for k,v in d['constants'].items()};gap=c['gap_q1'];eta=c['eta_nodes']
    assert gap==min(gap0,gap1)
    assert c['F2_quotient_norm']==B2 and c['F3_derivative_norm']==M3
    assert c['F3_at_r']==f3r and c['F3_lower_bound']==f3r/2
    assert eta<=F(1,64) and eta*M3<=f3r/2
    K=c['F3_lower_bound'];eps=c['epsilon_probability'];gamma=c['gamma_near_r'];C=c['Cstar'];b=c['target_base_b'];D=1-r-eta
    assert gamma==K/6 and c['r_node_complement_lower_bound']==D
    assert 0<eps<=F(1,2) and eps*B2/2<=F(1,4) and eps*B1/2<=K/6
    assert eps*B0<=F(1,32) and eps*B0<=2*eta**2*gap**2 and eps*B1<=32*eta**4*gap**2
    assert 0<C<=F(1,8) and C/gap<=eps/2
    assert B1*(32*B0)**2*C/D<=gamma/2
    assert b==1-C/8 and 0<b<1
    # -log(b)<= (1-b)/b, so the exact algebraic target's total log loss
    # satisfies 2(-log b)<C without computing any logarithm.
    assert 2*(1-b)/b<C
    for z in d['target']['moment_exponents']:
        l=z['lambda'];assert F(z['power_of_b'])==l+sum((r**i for i in range(l)),F(0))
    result={'status':'PASS','certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'reviewer_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'normal_shifted_nonzero_terms':shift_terms,'Cstar_numerator_bits':C.numerator.bit_length(),
            'Cstar_denominator_bits':C.denominator.bit_length(),'exact_target_total_loss_below_Cstar':True,
            'python':platform.python_version(),
            'scope':'Exact independent rational certificate checks; global logarithmic inequalities and all-factor rejection have separate hand proofs. No source-size screen or log-zero oracle.'}
    Path(__file__).with_name('paired-normal-head-review-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
