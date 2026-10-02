"""Baker projective-fiber pilots for killing, and drift-plus-killing quotients."""
from pathlib import Path
import json,time,resource
import sympy as S
resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(700*1024**2,700*1024**2))
t0=time.monotonic();r,x=S.symbols('r x');records=[]
for name in ['killing','drift_killing']:
    if name=='killing':
        A=S.Poly(sum(x**i for i in range(5)),x);B=S.Poly(sum(x**i for i in range(9)),x);den=x+1
    else:
        def R(n):return sum(x**i for i in range(n))
        def E(n):return S.div((n-1)*(R(3)-R(1))-2*(R(n)-R(1)),x*(1-x),x)[0]
        den=E(6);A=S.Poly(E(10),x);B=S.Poly(E(15),x)
    P=S.Poly(den.subs(x,r)*A.as_expr()-A.as_expr().subs(x,r)*den,x)
    Q=S.Poly(den.subs(x,r)*B.as_expr()-B.as_expr().subs(x,r)*den,x)
    U=P.exquo(S.Poly(x-r,x));V=Q.exquo(S.Poly(x-r,x))
    res=S.Poly(S.resultant(U,V,x),r);content,fs=S.factor_list(res)
    rec={'name':name,'denominator':str(den),'A':str(A.as_expr()),'B':str(B.as_expr()),
         'resultant_degree':int(res.degree()),'factorization':str(S.factor(res.as_expr())),
         'content':str(content),'factor_records':[{'degree':int(f.degree()),'multiplicity':int(e),
             'coefficients_descending':[str(c) for c in f.all_coeffs()],
             'negative_monomials':[[int(mon[0]),str(c)] for mon,c in f.terms() if c<0]} for f,e in fs],
         'seconds_from_start':time.monotonic()-t0}
    records.append(rec)
    print(json.dumps({'name':name,'degree':rec['resultant_degree'],'negative_factors':[(v['degree'],v['negative_monomials']) for v in rec['factor_records'] if v['negative_monomials']],'seconds':time.monotonic()-t0}),flush=True)
(root:=Path(__file__).parent).joinpath('residue-projective-flags-pilot.json').write_text(json.dumps({'status':'PASS exact projective resultants; positivity/source bridge separate','records':records,'seconds':time.monotonic()-t0},indent=2)+'\n')
