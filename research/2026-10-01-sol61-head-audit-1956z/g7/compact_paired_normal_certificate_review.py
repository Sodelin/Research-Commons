"""Independent check of the tighter cap-seven rational certificate.
Its derivative numerators are reconstructed independently with Fraction
polynomial arithmetic; all bounds and the 175-bit input are recomputed.
"""
import json,hashlib,platform
from fractions import Fraction as F
from pathlib import Path
from argparse import ArgumentParser
from collections import defaultdict
from paired_normal_certificate_review import sub,ev,divroot,mul

def multi_mul(a,b):
    out=defaultdict(F)
    for (ip,iq),x in a.items():
        for (jp,jq),y in b.items():out[ip+jp,iq+jq]+=x*y
    return {ij:x for ij,x in out.items() if x}

def derive_numerator(la,c):
    factors=[{(0,0):F(1),(1,0):F(-1),(1,l):F(1)} for l in la]
    squared=[multi_mul(f,f) for f in factors];raw=defaultdict(F)
    for j,(l,co) in enumerate(zip(la,c)):
        value={(1,2*l-2):F(l)}
        if l>1:value.update({(0,l-2):F(-l*(l-1)),(1,l-2):F(l*(l-1))})
        for k,f in enumerate(squared):
            if k!=j:value=multi_mul(value,f)
        for ij,x in value.items():raw[ij]+=co*x
    degp=max(ip for ip,iq in raw);degq=max(iq for ip,iq in raw);out={}
    for iq in range(degq+1):
        running=F(0)
        for ip in range(degp+1):
            running+=raw.get((ip,iq),F(0))
            if ip<degp and running:out[ip,iq]=running
        assert running==0 # exact division by (1-p)
    return out

def main():
    ap=ArgumentParser();ap.add_argument('--certificate',required=True);ap.add_argument('--prior');a=ap.parse_args()
    path=Path(a.certificate);d=json.loads(path.read_text());old=json.loads(Path(a.prior).read_text()) if a.prior else None
    polys={};coef={};terms={};widths=[]
    for tag,z in d['normal_records'].items():
        c=list(map(F,z['c']));la=z['exponents'];assert sum(c)==1 and sum(v*l for v,l in zip(c,la))==0
        if old:
            assert c==list(map(F,old[tag]['covector'])) and la==old[tag]['exponents']
            assert list(map(F,z['positive_quotient_coefficients']))==list(map(F,old[tag]['positive_quotient_coefficients']))
        oldN=derive_numerator(la,c)
        newN={tuple(t[0]):F(t[1]) for t in z['normalized_Lqq_numerator_terms']}
        assert newN==oldN
        one=defaultdict(F)
        for (ip,iq),v in newN.items():one[ip]+=v
        one={i:v for i,v in one.items() if v};k=-sum(v*l*l for v,l in zip(c,la))
        assert one=={0:k} and k>0 and k==F(z['F_second_derivative_at_one'])
        bound=sum(abs(v)*iq for (ip,iq),v in newN.items())
        assert bound==F(z['normalized_Lqq_numerator_q_derivative_L1_bound'])
        width=F(z['near_one_width']);assert width<=F(1,8) and width*bound<=k/2
        widths.append(width);coef[tag]=sum(abs(v) for v in c);assert coef[tag]==F(z['coefficient_L1'])
        polys[tag]={0:F(1),**{l:-v for v,l in zip(c,la)}};terms[tag]=len(newN)
        factors={0:F(1)}
        for a0,b0 in [(F(1),F(-1)),(F(2),F(-1))]+([(F(4),F(-1))] if tag=='F1' else []):
            factors=mul(factors,mul({1:a0,0:b0},{1:a0,0:b0}))
        qc=list(map(F,z['positive_quotient_coefficients']));assert all(v>0 for v in qc)
        assert mul(factors,{len(qc)-1-i:v for i,v in enumerate(qc)})==polys[tag]
    c={k:F(v) for k,v in d['constants'].items()};f=polys['F1'];r=F(1,2)
    second=sub({j:2*v for j,v in f.items()},{2*j:v for j,v in f.items()})
    D=sum(abs(v) for v in divroot(divroot(second,r),r).values())
    third=sub(sub({j:3*v for j,v in f.items()},{2*j:3*v for j,v in f.items()}),{3*j:-v for j,v in f.items()})
    Kr=ev(third,r);MK=sum(abs(j*v) for j,v in third.items())
    assert Kr==ev(f,r**3)>0
    width=c['near_one_width'];eta=c['root_interval_half_width'];A=c['A'];K=c['K_lower_bound'];B0=coef['F0'];B1=coef['F1']
    assert width==min(widths) and c['Q']==1-width and c['Q']>=F(7,8)
    assert eta<=F(1,32) and eta*MK<=Kr/2 and K==Kr/2
    assert c['T12_divided_square_coefficient_L1']==D and c['T13_derivative_L1']==MK and c['T13_at_r']==Kr
    assert A==4*F(15,32)**2*F(7,8)**2 and c['V_F0_lower_bound']==4*F(23,32)**2*F(7,32)**2
    assert c['outside_U_F0_lower_bound']==4*width**2*eta**2 and c['outside_UV_F1_lower_bound']==64*width**2*eta**4
    p0=c['p0'];delta=c['delta'];gamma=c['gamma'];C=c['C_star']
    assert 0<p0<=F(1,2) and p0*D<=A and p0*B1<=K/3
    assert p0*B0<=c['V_F0_lower_bound']/2 and delta==c['V_F0_lower_bound']/2
    assert p0*B0<=c['outside_U_F0_lower_bound']/2 and p0*B1<=c['outside_UV_F1_lower_bound']/2
    assert gamma==K/6 and 0<C<=p0*width and B1*(B0/delta)**2*C/F(15,32)<=gamma/2
    target=d['algebraic_input'];N=target['N'];b=F(int(target['b_numerator']),int(target['b_denominator']))
    assert N==175 and b==1-F(1,2)**N and 0<b<1
    assert 2*(1-b)/b<4*F(1,2)**N<C
    result={'status':'PASS','certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'reviewer_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'independently_rederived_normal_numerator_terms':terms,'target_b':'1-2^(-175)',
            'certified_total_log_loss_below_Cstar':True,'Cstar_numerator_bits':C.numerator.bit_length(),
            'Cstar_denominator_bits':C.denominator.bit_length(),'python':platform.python_version(),
            'scope':'Independent exact rational bounds and concrete algebraic target; no finite-source census or log-sign approximation.'}
    Path(__file__).with_name('compact-paired-normal-head-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
