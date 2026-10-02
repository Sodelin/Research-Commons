"""Exact finite certificates for supplied dyadic Poisson flags/count.

The analytic/all-factor/closure transfer remains the separate hand theorem.
This is not a factor census or numerical fit. Run one supplied case at a time.
"""
import hashlib
import json
import math
import platform
import sys
from pathlib import Path
import sympy as S

s_count=int(sys.argv[1]) if len(sys.argv)>1 else 1
alpha=int(sys.argv[2]) if len(sys.argv)>2 else 0
beta=int(sys.argv[3]) if len(sys.argv)>3 else 0
r=S.Rational(sys.argv[4]) if len(sys.argv)>4 else S.Rational(1,2)
assert s_count>=1 and alpha in [0,1] and beta in [0,1] and 0<r<1
p,q=S.symbols('p q')
nodes=[r**(2**j) for j in range(s_count)]
new=nodes[-1]**2
all_nodes=nodes+[new]
cap=2*s_count+alpha+beta+4
la=[j*(j-1)//2 for j in range(2,cap+1)]
d0=2*s_count+beta+2
records={}
polys={}

def first_derivative_numerator(c,ls,sign):
    fs=[S.Poly(1-p+p*q**l,p,q) for l in ls]
    out=S.Poly(0,p,q)
    for j,(x,l) in enumerate(zip(c,ls)):
        value=S.Poly(sign*x*l*q**(l-1),p,q)
        for k,f in enumerate(fs):
            if k!=j:value*=f
        out+=value
    return out

for name,length,roots,root_order in [
        ('F0',d0,nodes,2),('F1',len(la),all_nodes,1+alpha)]:
    ls=la[:length]
    rows=[];rhs=[]
    if root_order==2: rows.append(ls);rhs.append(0)
    if beta: rows.append([1]*length);rhs.append(0)
    for node in roots:
        rows += [[1-node**l for l in ls],[-l*node**(l-1) for l in ls]]
        rhs += [0,0]
    rows.append([-1]+[0]*(length-1) if beta else [1]*length)
    rhs.append(1)
    assert len(rows)==length
    c=list(S.Matrix(rows).inv()*S.Matrix(rhs))
    F=S.Poly(sum(x*(1-q**l) for x,l in zip(c,ls)),q)
    root_factor=q**beta*(1-q)**root_order
    for node in roots:root_factor*=(q-node)**2
    quotient,rem=F.div(S.Poly(root_factor,q))
    assert rem.is_zero and quotient.eval(0)>0
    assert all(x>=0 for x in quotient.all_coeffs())
    projection=sum(x*l for x,l in zip(c,ls))
    assert projection==0 if root_order==2 else projection>0
    near_zero=None
    if beta:
        numerator0=first_derivative_numerator(c,ls,-1)
        at_zero=S.Poly(numerator0.as_expr().subs(q,0),p)
        assert S.expand(at_zero.as_expr()-(1-p)**(length-1))==0
        M0=sum(abs(v)*powers[1] for powers,v in numerator0.terms())
        near_zero=min(new/4,S.Rational(1,2)**(length-1)/(2*M0))
    if root_order==1:
        numerator=first_derivative_numerator(c,ls,1)
        constant=projection
        order=1
    else:
        fs=[S.Poly(1-p+p*q**l,p,q) for l in ls]
        squared=[f*f for f in fs]
        raw=S.Poly(0,p,q)
        for j,(x,l,f) in enumerate(zip(c,ls,fs)):
            term=p*p*l*l*q**(2*l-2)
            if l>1:term-=p*l*(l-1)*q**(l-2)*f.as_expr()
            value=S.Poly(x*term,p,q)
            for k,fac in enumerate(squared):
                if k!=j:value*=fac
            raw+=value
        numerator,rem=raw.div(S.Poly(p*(1-p),p,q))
        assert rem.is_zero
        constant=F.diff().diff().eval(1)
        order=2
    assert constant>0 and S.Poly(numerator.as_expr().subs(q,1),p).as_expr()==constant
    M=sum(abs(v)*powers[1] for powers,v in numerator.terms())
    near_one=min((1-max(all_nodes))/4,constant/(2*M))
    rec={'exponents':ls,'c':[str(x) for x in c],
         'root_at_one_order':root_order,'lambda_projection':str(projection),
         'positive_quotient_coefficients':[str(x) for x in quotient.all_coeffs()],
         'quotient_at_zero':str(quotient.eval(0)),
         'near_one_derivative_order':order,'near_one_constant':str(constant),
         'near_one_numerator_terms':[[list(a),str(v)] for a,v in numerator.terms()],
         'near_one_derivative_L1':str(M),'near_one_width':str(near_one),
         'coefficient_L1':str(sum(abs(x) for x in c))}
    if beta:rec.update({'near_zero_width':str(near_zero),
         'near_zero_numerator_terms':[[list(a),str(v)] for a,v in numerator0.terms()],
         'near_zero_derivative_L1':str(M0),
         'near_zero_constant_lower_bound':str(S.Rational(1,2)**(length-1))})
    records[name]=rec;polys[name]=F.as_expr()

width=min(S.Rational(records[n]['near_one_width']) for n in records)
lower=min(S.Rational(records[n]['near_zero_width']) for n in records) if beta else S.Rational(0)
ordered=sorted([S.Rational(0)]+all_nodes+[S.Rational(1)])
eta0=min(b-a for a,b in zip(ordered,ordered[1:]))/8
F1=polys['F1'];G=S.Poly(2*F1-F1.subs(q,q*q),q)
Kpoly=S.Poly(3*F1-3*F1.subs(q,q*q)+F1.subs(q,q**3),q)
MK=sum(abs(v)*a[0] for a,v in Kpoly.terms())
quot1=S.Rational(records['F1']['quotient_at_zero'])
quot0=S.Rational(records['F0']['quotient_at_zero'])
A_values=[];D_values=[];K_values=[]
for node in nodes:
    gquot,rem=G.div(S.Poly((q-node)**2,q));assert rem.is_zero
    D_values.append(sum(abs(v) for v in gquot.all_coeffs()))
    kval=Kpoly.eval(node);assert kval==F1.subs(q,node**3) and kval>0
    K_values.append(kval)
    bound=quot1*(node-eta0)**beta*(1-node-eta0)**(1+alpha)
    for other in all_nodes:
        if other!=node:bound*=(abs(node-other)-eta0)**2
    assert bound>0;A_values.append(bound)
eta=min(eta0,min(K_values)/(2*MK))
A=min(A_values);D=max(D_values);K=min(K_values)/2
B0=S.Rational(records['F0']['coefficient_L1'])
B1=S.Rational(records['F1']['coefficient_L1'])
Vmin=quot0*(new-eta0)**beta*(1-new-eta0)**2
for node in nodes:Vmin*=(abs(new-node)-eta0)**2
outside0=quot0*(lower**beta)*width**2*eta**(2*s_count)
outside1=quot1*(lower**beta)*width**(1+alpha)*eta**(2*(s_count+1))
assert outside0>0 and outside1>0
p0=min(S.Rational(1,2),A/D,K/(3*B1),Vmin/(2*B0),outside0/(2*B0),outside1/(2*B1))
delta=Vmin/2;gamma=K/6
massK=1/(1-max(nodes)-eta)
Cstar=min(p0*width,gamma/(2*B1*(B0/delta)**2*massK))
if beta:Cstar=min(Cstar,(1-lower)/2)
assert 0<Cstar<1
mult=s_count+alpha+beta;N=2
while 2*mult*S.Rational(1,2)**N>=Cstar:N+=1
b=1-S.Rational(1,2)**N
E=[alpha*l+beta+sum(sum(node**k for k in range(l)) for node in nodes) for l in la]
assert E[0]==mult and b**mult>1-Cstar/2
integer_rows=[]
for name in ['F0','F1']:
    c=[S.Rational(x) for x in records[name]['c']]
    den=S.ilcm(*(S.denom(x) for x in c));raw=[int(den*x) for x in c]
    common=math.gcd(*raw);row=[v//common for v in raw]+[0]*(len(la)-len(raw))
    assert sum(x*y for x,y in zip(row,E))==0
    integer_rows.append(row)
assert E[1]!=3*E[0]
out={'status':'PASS exact finite parameter certificate','s':s_count,'alpha':alpha,'beta':beta,
     'r':str(r),'nodes':[str(x) for x in nodes],'NO_cap':cap,'attainment_through_cap':cap-1,
     'normal_records':records,
     'constants':{k:str(v) for k,v in {'upper_width':width,'lower_corner_width':lower,
         'eta0':eta0,'eta':eta,'A':A,'D':D,'K':K,'MK':MK,'B0':B0,'B1':B1,
         'Vmin':Vmin,'outside0':outside0,'outside1':outside1,'p0':p0,
         'delta':delta,'gamma':gamma,'mass_K':massK,'C_star':Cstar}.items()},
     'algebraic_input':{'b':f'1-2^(-{N})','N':N,'exponents':la,
         'signature_rational_exponents':[str(x) for x in E],
         'primitive_integer_normal_rows':integer_rows,'strict_cutoff_verified':True},
     'python':platform.python_version(),'sympy':S.__version__,
     'scope':'Finite exact polynomial/rational premises and algebraic exponent identities. Analytic/global all-N and ordinary-interior transfer are hand proofs; general recognition remains open.'}
tag=f'dyadic-s{s_count}-a{alpha}-k{beta}'
path=Path(__file__).with_name(tag+'-certificate.json')
path.write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','case':tag,'NO_cap':cap,'b_N':N,
    'normalized_terms':{n:len(x['near_one_numerator_terms']) for n,x in records.items()},
    'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}))
