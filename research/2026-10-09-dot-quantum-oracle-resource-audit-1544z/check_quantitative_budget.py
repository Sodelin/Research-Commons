"""Exact rational truncation-budget check, not a synthesis implementation."""
from fractions import Fraction
import json
rows=[]
for n in [1,2,3,4,8]:
    for eps in [Fraction(1,2),Fraction(1,10),Fraction(1,100),Fraction(1,1024)]:
        M=4096*(n+1)**2
        J=8*M*(n+1)
        L=1
        while 18*J*Fraction(3,4)**L>eps/8: L+=1
        assert 18*J*Fraction(3,4)**L<=eps/8
        assert L==1 or 18*J*Fraction(3,4)**(L-1)>eps/8
        hlog=L.bit_length() # ceil(log2(L+1)) for positive integer L
        b=n*L+hlog
        K=b*(L+1)
        rows.append({'n':n,'epsilon':str(eps),'J':J,'L':L,'b':b,'K':K,
                     'minimal_positive_L':True,'exact_truncation_budget_pass':True})
print(json.dumps({'status':'PASS','arithmetic':'Python fractions, exact rational',
                  'scope':'Only the displayed truncation budget, minimal L and register-size arithmetic. No slot generator, net, ETR, oracle evaluator, quantum compiler or Lean run.',
                  'cases':rows},indent=2))
