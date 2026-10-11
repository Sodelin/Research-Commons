"""dot / OpenAI. Read-only arithmetic diagnostic of the supplied PR377 profile.
Decimal logarithms are numerical diagnostics, not certified interval bounds.
No external repository code is executed.
"""
from fractions import Fraction
from decimal import Decimal, localcontext
import json
counts={1:157599,2:43488,3:37296,4:10080,5:15480,6:23832,7:3096,8:7488,9:576,16:3840,32:3840,48:3840}
m,W=73,14727
S=sum(r*c for r,c in counts.items())
q=Fraction(S,m*W)
assert S==1072575 and m*W-S==2496 and 0<q<1
assert all(0<r<m and c>0 for r,c in counts.items())
rows=[]
for precision in (40,80):
 with localcontext() as ctx:
  ctx.prec=precision
  mean=sum(Decimal(r*c)/Decimal(S)*(Decimal(m)/Decimal(r)).ln() for r,c in counts.items())
  bound=-(Decimal(q.numerator)/Decimal(q.denominator)).ln()/mean
  b=Decimal(999240641319551)/Decimal(10**18)
  rows.append({'decimal_precision':precision,'mean_log':str(mean),'jensen_upper_diagnostic':str(bound),'published_coarse_b':str(b),'relative_excess_percent':str(100*(bound/b-1))})
print(json.dumps({'status':'EXACT_RATIONAL_COUNTS_PASS_NUMERICAL_LOG_DIAGNOSTIC_ONLY','rank_mass':S,'denominator':m*W,'mass_gap':m*W-S,'q_numerator':q.numerator,'q_denominator':q.denominator,'rows':rows},indent=2))
