"""Exact rational uniform constants for the global cap-seven hand theorem.

No factor census or floating fit. This verifies the finite polynomial premises
and extracts an exact algebraic input family using the hand sum/budget proof.
"""
import hashlib
import json
import platform
from pathlib import Path
import sympy as S

ROOT=Path(__file__).parent
src=ROOT/'paired-normal-algebra.json'
data=json.loads(src.read_text())
p,q=S.symbols('p q')
r=S.Rational(1,2); node2=r*r
records={}
polys={}
for name in ['F0','F1']:
    ls=data[name]['exponents']
    c=[S.Rational(x) for x in data[name]['c']]
    assert sum(c)==1 and sum(x*l for x,l in zip(c,ls))==0
    F=S.Poly(1-sum(x*q**l for x,l in zip(c,ls)),q)
    assert F.eval(r)==0 and F.diff().eval(r)==0
    if name=='F1':
        assert F.eval(node2)==0 and F.diff().eval(node2)==0
    neutral=(1-q)**2*4*(q-r)**2
    if name=='F1': neutral*=16*(q-node2)**2
    quotient,remainder=F.div(S.Poly(neutral,q))
    assert remainder.is_zero
    assert quotient.eval(0)==1 and all(x>0 for x in quotient.all_coeffs())
    ff=[1-p+p*q**l for l in ls]
    squared=[S.Poly(f*f,p,q) for f in ff]
    raw=S.Poly(0,p,q)
    for j,(x,l,f) in enumerate(zip(c,ls,ff)):
        term=p*p*l*l*q**(2*l-2)
        if l>1: term-=p*l*(l-1)*q**(l-2)*f
        value=S.Poly(x*term,p,q)
        for k,fac in enumerate(squared):
            if k!=j:value*=fac
        raw+=value
    numerator,rem=raw.div(S.Poly(p*(1-p),p,q))
    assert rem.is_zero
    at_one=S.Poly(numerator.as_expr().subs(q,1),p)
    Fpp=F.diff().diff().eval(1)
    assert Fpp>0 and at_one.as_expr()==Fpp
    Mq=sum(abs(coef)*powers[1] for powers,coef in numerator.terms())
    assert Mq>0
    records[name]={'exponents':ls,'c':[str(x) for x in c],
        'positive_quotient_coefficients':[str(x) for x in quotient.all_coeffs()],
        'F_second_derivative_at_one':str(Fpp),
        'normalized_Lqq_numerator_terms':
            [[list(powr),str(coef)] for powr,coef in numerator.terms()],
        'normalized_Lqq_numerator_q_derivative_L1_bound':str(Mq),
        'near_one_width':str(min(S.Rational(1,8),Fpp/(2*Mq))),
        'coefficient_L1':str(sum(abs(x) for x in c))}
    polys[name]=F.as_expr()

width=min(S.Rational(records[n]['near_one_width']) for n in records)
Q=1-width
assert Q>=S.Rational(7,8)
F1=polys['F1']
G=S.Poly(2*F1-F1.subs(q,q*q),q)
Gquot,Grem=G.div(S.Poly((q-r)**2,q))
assert Grem.is_zero
D=sum(abs(x) for x in Gquot.all_coeffs())
Kpoly=S.Poly(3*F1-3*F1.subs(q,q*q)+F1.subs(q,q**3),q)
Kr=Kpoly.eval(r)
assert Kr==F1.subs(q,r**3) and Kr>0
MK=sum(abs(coef)*power[0] for power,coef in Kpoly.terms())
eta=min(S.Rational(1,32),Kr/(2*MK))
K=Kr/2
A=4*S.Rational(15,32)**2*S.Rational(7,8)**2
B0=S.Rational(records['F0']['coefficient_L1'])
B1=S.Rational(records['F1']['coefficient_L1'])
Vmin=4*S.Rational(23,32)**2*S.Rational(7,32)**2
outside0=4*width**2*eta**2
outside1=64*width**2*eta**4
p0=min(S.Rational(1,2),A/D,K/(3*B1),Vmin/(2*B0),
       outside0/(2*B0),outside1/(2*B1))
delta=Vmin/2
gamma=K/6
Cstar=min(p0*width,gamma*S.Rational(15,32)/(2*B1*(B0/delta)**2))
assert all(x>0 for x in [width,eta,A,D,K,B0,B1,p0,delta,gamma,Cstar])
N=2
while 4*S.Rational(1,2)**N>=Cstar:N+=1
tiny=S.Rational(1,2)**N
assert tiny<=S.Rational(1,2) and 4*tiny<Cstar
b=1-tiny
out={'status':'PASS finite rational/polynomial certificate',
     'python':platform.python_version(),'sympy':S.__version__,
     'input_normal_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),
     'normal_records':records,
     'constants':{k:str(v) for k,v in {
        'near_one_width':width,'Q':Q,'root_interval_half_width':eta,
        'A':A,'T12_divided_square_coefficient_L1':D,
        'T13_at_r':Kr,'T13_derivative_L1':MK,'K_lower_bound':K,
        'B0':B0,'B1':B1,'V_F0_lower_bound':Vmin,
        'outside_U_F0_lower_bound':outside0,
        'outside_UV_F1_lower_bound':outside1,
        'p0':p0,'delta':delta,'gamma':gamma,'C_star':Cstar}.items()},
     'algebraic_input':{'cap':7,'exponents':[1,3,6,10,15,21],
        'N':N,'b_formula':f'1-2^(-{N})',
        'b_numerator':str(S.numer(b)),'b_denominator':str(S.denom(b)),
        'signature_formula':'m_lambda=b^(lambda+2-2^(1-lambda))',
        'compact_exact_encoding':'z_0=b; z_(k+1)>0 and z_(k+1)^2=z_k; m_lambda=b^(lambda+2)/z_(lambda-1)',
        'first_loss_upper_bound':str(4*tiny),
        'verified_upper_bound_below_Cstar':bool(4*tiny<Cstar)},
     'scope':'Finite polynomial/rational premises and exact example extraction. Nonattainment, ordinary interior, closure and all-N summation are separate hand proofs. No formal Lean proof.'}
(ROOT/'paired-normal-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'PASS','N':N,'normal_numerator_terms':
    {k:len(v['normalized_Lqq_numerator_terms']) for k,v in records.items()},
    'Cstar_numerator_bits':int(S.numer(Cstar)).bit_length(),
    'Cstar_denominator_bits':int(S.denom(Cstar)).bit_length()}))
