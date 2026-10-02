"""Bounded all-parameter one-residue flag pilots; no source transfer by association."""
from pathlib import Path
import argparse,itertools,json,hashlib,time,resource
import sympy as S
ap=argparse.ArgumentParser();ap.add_argument('--alpha',type=int,required=True);ap.add_argument('--beta',type=int,required=True);args=ap.parse_args()
a,b=args.alpha,args.beta
assert a in [0,1] and b in [0,1] and (a,b)!=(1,0)
resource.setrlimit(resource.RLIMIT_CPU,(90,90));resource.setrlimit(resource.RLIMIT_AS,(900*1024**2,900*1024**2))
t0=time.monotonic();root=Path(__file__).parent;r,p=S.symbols('r p');cap=6+a+b;ls=[j*(j-1)//2 for j in range(2,cap+1)];d=len(ls)
if b==0:norm=[1]*d;norm_name='sum c=1'
elif a==0:norm=ls[:];norm_name='c.lambda=1'
else:norm=[1]+[0]*(d-1);norm_name='c_0=1'
rows=[[S.Poly(x,r) for x in norm]]
if b:rows.append([S.Poly(1,r) for l in ls])
if a:rows.append([S.Poly(l,r) for l in ls])
rows += [[S.Poly(1-r**l,r) for l in ls],[S.Poly(l*r**(l-1),r) for l in ls],
         [S.Poly(1-r**(2*l),r) for l in ls],[S.Poly(l*r**(2*l-2),r) for l in ls]]
assert len(rows)==d
C=[]
for i in range(d):
    cols=[j for j in range(d) if j!=i];v=S.Poly(0,r)
    for perm in itertools.permutations(cols):
        inv=sum(perm[j]>perm[k] for j in range(d-1) for k in range(j+1,d-1))
        term=S.Poly((-1)**(inv+i),r)
        for k,j in enumerate(perm):term*=rows[k+1][j]
        v+=term
    C.append(v)
D=sum((rows[0][i]*C[i] for i in range(d)),S.Poly(0,r))
assert all(sum((rows[k][i]*C[i] for i in range(d)),S.Poly(0,r)).is_zero for k in range(1,d))
g=C[0]
for v in C[1:]:g=S.gcd(g,v)
B=[v.exquo(g) for v in C]
print(json.dumps({'stage':'normal','flags':[a,b],'B_degrees':[int(v.degree()) for v in B],'seconds':time.monotonic()-t0}),flush=True)
base={'flags':[a,b],'cap':cap,'lambda':ls,'normalization':norm_name,
      'C_degrees':[int(v.degree()) for v in C],'D_degree':int(D.degree()),
      'common_factor':str(S.factor(g.as_expr())),
      'B_coefficients_descending':[[str(x) for x in v.all_coeffs()] for v in B],
      'D_div_common_factor':str(S.factor(D.exquo(g).as_expr()))}
records=[];Elist=[];domain=S.ZZ.poly_ring(r)
for z in [3,5]:
    P=S.Poly(0,p,domain=domain);Q0=P
    ff=[S.Poly(1-p+p*z**l,p,domain=domain) for l in ls]
    for i,l in enumerate(ls):
        term=S.Poly(1,p,domain=domain)
        for j in range(d):
            if j!=i:term*=ff[j]
        P+=term.mul_ground(B[i].as_expr()*(1-z**l))
        Q0+=term.mul_ground(B[i].as_expr()*l*z**(l-1))
    Q=Q0.exquo(S.Poly(1-p,p,domain=domain)) if a else Q0
    assert P.degree()==d-1-b and Q.degree()==d-1-a
    res=S.Poly(P.resultant(Q),r,domain=S.ZZ);content,primitive=res.primitive()
    records.append({'q_slice':z,'P_p_degree':int(P.degree()),'Q_p_degree':int(Q.degree()),
        'resultant_degree':int(res.degree()),'content':str(content),
        'primitive_coefficients_descending':[str(x) for x in primitive.all_coeffs()]})
    Elist.append(primitive)
    print(json.dumps({'stage':'resultant','flags':[a,b],'q':z,'degree':int(res.degree()),'seconds':time.monotonic()-t0}),flush=True)
G=S.gcd(*Elist);gc,facs=S.factor_list(G)
base.update({'status':'PASS exact one-residue flag algebra; positivity/source consequence separate',
             'resultants':records,'gcd_degree':int(G.degree()),'gcd_factorization':str(S.factor(G.as_expr())),
             'gcd_coefficients_descending':[str(x) for x in G.all_coeffs()],
             'factor_records':[{'degree':int(f.degree()),'multiplicity':int(e),'coefficients_descending':[str(x) for x in f.all_coeffs()],
                                'negative_monomials':[[int(mon[0]),str(c)] for mon,c in f.terms() if c<0]} for f,e in facs],
             'seconds':time.monotonic()-t0,'sympy':S.__version__})
(root/f'flags-{a}-{b}-pilot.json').write_text(json.dumps(base,indent=2)+'\n')
print(json.dumps({'status':base['status'],'flags':[a,b],'gcd_degree':base['gcd_degree'],'negative_factors':[(x['degree'],x['negative_monomials']) for x in base['factor_records'] if x['negative_monomials']],'seconds':base['seconds']}),flush=True)
