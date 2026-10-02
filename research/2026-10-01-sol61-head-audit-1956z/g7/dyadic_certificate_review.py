"""Independent exact checks of supplied dyadic-family finite certificates.
The arbitrary-s analytic/source theorem is reviewed separately.
"""
import json,hashlib,math,platform
from pathlib import Path
from fractions import Fraction as F
from collections import defaultdict
from argparse import ArgumentParser
from paired_normal_certificate_review import mul,sub,divroot,ev
from compact_paired_normal_certificate_review import derive_numerator,multi_mul

def first_numerator(la,c,sign):
    fs=[{(0,0):F(1),(1,0):F(-1),(1,l):F(1)} for l in la];out=defaultdict(F)
    for j,(l,co) in enumerate(zip(la,c)):
        value={(0,l-1):sign*co*l}
        for k,f in enumerate(fs):
            if k!=j:value=multi_mul(value,f)
        for ij,v in value.items():out[ij]+=v
    return {ij:v for ij,v in out.items() if v}
def at_q(N,q):
    out=defaultdict(F)
    for (ip,iq),v in N.items():out[ip]+=v*q**iq
    return {ip:v for ip,v in out.items() if v}

def review(path):
    d=json.loads(path.read_text());s,a,beta=d['s'],d['alpha'],d['beta'];r=F(d['r']);nodes=list(map(F,d['nodes']));new=nodes[-1]**2
    assert nodes==[r**(2**j) for j in range(s)] and d['NO_cap']==2*s+a+beta+4
    assert d['attainment_through_cap']==d['NO_cap']-1
    f={};B={};widths=[];zeros=[]
    for tag,z in d['normal_records'].items():
        la=z['exponents'];c=list(map(F,z['c']));roots=nodes if tag=='F0' else nodes+[new];order=2 if tag=='F0' else 1+a
        assert z['root_at_one_order']==order
        poly={0:sum(c),**{l:-v for l,v in zip(la,c)}}
        factor={beta:F(1)}
        for _ in range(order):factor=mul(factor,{0:F(1),1:F(-1)})
        for node in roots:factor=mul(factor,mul({0:-node,1:F(1)},{0:-node,1:F(1)}))
        qc=list(map(F,z['positive_quotient_coefficients']));assert all(v>=0 for v in qc) and qc[-1]>0
        assert mul(factor,{len(qc)-1-i:v for i,v in enumerate(qc)})=={i:v for i,v in poly.items() if v}
        if beta:assert sum(c)==0 and -c[0]==1
        else:assert sum(c)==1
        projection=sum(v*l for v,l in zip(c,la));assert projection==F(z['lambda_projection'])
        assert projection==0 if order==2 else projection>0
        N={tuple(t[0]):F(t[1]) for t in z['near_one_numerator_terms']}
        assert N==(derive_numerator(la,c) if order==2 else first_numerator(la,c,1))
        value= -sum(v*l*l for v,l in zip(c,la)) if order==2 else projection
        assert at_q(N,F(1))=={0:value} and value>0
        norm=sum(abs(v)*iq for (ip,iq),v in N.items());width=F(z['near_one_width'])
        assert norm==F(z['near_one_derivative_L1']) and width*norm<=value/2
        assert width<=(1-max(nodes+[new]))/4
        assert F(z['quotient_at_zero'])==qc[-1]
        assert F(z['coefficient_L1'])==sum(abs(v) for v in c)
        widths.append(width)
        if beta:
            N0={tuple(t[0]):F(t[1]) for t in z['near_zero_numerator_terms']}
            assert N0==first_numerator(la,c,-1)
            assert at_q(N0,F(0))=={i:F((-1)**i*math.comb(len(la)-1,i)) for i in range(len(la))}
            norm0=sum(abs(v)*iq for (ip,iq),v in N0.items());zero=F(z['near_zero_width'])
            assert norm0==F(z['near_zero_derivative_L1']) and zero*norm0<=F(1,2)**len(la)
            assert zero<=new/4
            zeros.append(zero)
        f[tag]=poly;B[tag]=sum(abs(v) for v in c)
    c={k:F(v) for k,v in d['constants'].items()};assert c['upper_width']==min(widths)
    assert c['lower_corner_width']==(min(zeros) if beta else 0)
    second=sub({i:2*v for i,v in f['F1'].items()},{2*i:v for i,v in f['F1'].items()})
    third=sub(sub({i:3*v for i,v in f['F1'].items()},{2*i:3*v for i,v in f['F1'].items()}),{3*i:-v for i,v in f['F1'].items()})
    Ds=[];Ks=[]
    for node in nodes:
        Ds.append(sum(abs(v) for v in divroot(divroot(second,node),node).values()))
        value=ev(third,node);assert value==ev(f['F1'],node**3)>0;Ks.append(value)
    MK=sum(abs(i*v) for i,v in third.items());assert c['D']==max(Ds) and c['K']==min(Ks)/2 and c['MK']==MK
    assert c['eta']*MK<=min(Ks)/2 and 0<c['eta']<=c['eta0']
    ordered=sorted([F(0)]+nodes+[new,F(1)])
    eta0=min(y-x for x,y in zip(ordered,ordered[1:]))/8
    assert c['eta0']==eta0
    q0=F(d['normal_records']['F0']['quotient_at_zero'])
    q1=F(d['normal_records']['F1']['quotient_at_zero'])
    AV=[]
    for node in nodes:
        bound=q1*(node-eta0)**beta*(1-node-eta0)**(1+a)
        for other in nodes+[new]:
            if other!=node:bound*=(abs(node-other)-eta0)**2
        AV.append(bound)
    vm=q0*(new-eta0)**beta*(1-new-eta0)**2
    for node in nodes:vm*=(abs(new-node)-eta0)**2
    outside0=q0*c['lower_corner_width']**beta*c['upper_width']**2*c['eta']**(2*s)
    outside1=q1*c['lower_corner_width']**beta*c['upper_width']**(1+a)*c['eta']**(2*(s+1))
    assert c['A']==min(AV)>0 and c['Vmin']==vm>0
    assert c['outside0']==outside0>0 and c['outside1']==outside1>0
    assert c['B0']==B['F0'] and c['B1']==B['F1']
    p0=c['p0'];C=c['C_star'];delta=c['delta'];gamma=c['gamma'];mass=c['mass_K']
    assert 0<p0<=F(1,2) and p0*c['D']<=c['A'] and p0*B['F1']<=c['K']/3
    assert p0*B['F0']<=c['Vmin']/2 and p0*B['F0']<=c['outside0']/2 and p0*B['F1']<=c['outside1']/2
    assert delta==c['Vmin']/2 and gamma==c['K']/6 and mass==1/(1-max(nodes)-c['eta'])
    assert 0<C<1 and C<=p0*c['upper_width'] and B['F1']*(B['F0']/delta)**2*mass*C<=gamma/2
    if beta:assert C<=(1-c['lower_corner_width'])/2
    inp=d['algebraic_input'];N=inp['N'];tiny=F(1,2)**N;mult=s+a+beta
    assert 2*mult*tiny<C
    la=inp['exponents'];E=list(map(F,inp['signature_rational_exponents']))
    assert E==[a*l+beta+sum(sum((q**j for j in range(l)),F(0)) for q in nodes) for l in la]
    assert E[0]==mult and E[1]!=3*E[0]
    for row in inp['primitive_integer_normal_rows']:assert sum(v*w for v,w in zip(row,E))==0
    return {'file':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'s':s,'alpha':a,'beta':beta,'NO_cap':d['NO_cap'],'b_N':N,'PASS':True}

def main():
    ap=ArgumentParser();ap.add_argument('--source-dir',required=True);a=ap.parse_args()
    paths=sorted(Path(a.source_dir).glob('dyadic-*-certificate.json'));assert paths
    result={'status':'PASS','certificates':[review(p) for p in paths],
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'python':platform.python_version(),
            'scope':'Independent exact finite certificate checks, including derivative reconstruction and endpoint/budget constants; arbitrary-family IFT/source/closure transfer has separate hand proof.'}
    Path(__file__).with_name('dyadic-head-review-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
