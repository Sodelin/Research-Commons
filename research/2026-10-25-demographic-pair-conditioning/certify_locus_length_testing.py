"""Exact sufficient-count probability enclosures for changed locus lengths."""
from fractions import Fraction as F
from math import comb,factorial
from pathlib import Path
import json
import certify_unknown_calendar_inverse as ci
# Upgrade precision at runtime, preserving the previously published engine bytes.
ci.Q=2**512
I=ci.I
def expneg_scalar(x):
 assert x>=0;k=0
 while x>1:x/=2;k+=1
 hi=sum((-x)**j/F(factorial(j)) for j in range(101));lo=hi+(-x)**101/F(factorial(101));r=I(lo,hi)
 for _ in range(k):r=r*r
 return r
ci.expneg_scalar=expneg_scalar

def probs(z,L):
 moments=[I(1)]+[ci.phi([I(v) for v in z],a) for a in range(1,L+1)]
 p=[]
 for k in range(L+1):
  coeff=[0]*(L+1)
  for i in range(k+1):
   for j in range(L-k+1):coeff[i+j]+=comb(k,i)*3**i*comb(L-k,j)*(-1)**j
  factor=F(comb(L,k)*3**(L-k),4**L)
  p.append(sum(factor*c*moments[i] for i,c in enumerate(coeff)))
 assert all(v.lo>0 for v in p)
 total=sum(p);assert total.lo<=1<=total.hi
 return p
source=[F(1),F(2),F(1)];design=json.loads(Path(__file__).with_name('locus-length-fisher-design.json').read_text());rows=[]
for L in [3,12,64,128]:
 row=next(r for r in design['rows'] if r['L']==L);rival=list(map(F,row['rival_rational']));assert rival[1]-source[1]==F(1,5)
 p,q=probs(source,L),probs(rival,L);chi=sum((b-a).absmax()**2/a.lo for a,b in zip(p,q));scale=10**30;chi=F((chi*scale).__ceil__(),scale)
 loci=(F(81,50)/chi).__ceil__()
 rows.append({'L':L,'source':list(map(str,source)),'rival':list(map(str,rival)),'target_eta':'1/10','chi_square_upper':str(chi),'necessary_loci_at_least':loci,'necessary_nucleotide_calls_at_least':2*L*loci,'minimum_source_probability_lower':str(min(v.lo for v in p)),'maximum_probability_interval_width':str(max(v.hi-v.lo for v in p+q))})
out={'status':'passed exact outward rational sufficient-law controls','arithmetic':'dyadic outward rounding denominator 2^512; exponential degree 100/101 alternating enclosure, scaling/squaring; exact polynomial coefficients','rows':rows,'limitations':'Separate actual rival for each design; lower bounds alone cannot rank attainable sample complexity or show optimal design. Full interval law probabilities recomputable from script.'}
Path(__file__).with_name('locus-length-testing-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{k:r[k] for k in ['L','necessary_loci_at_least','necessary_nucleotide_calls_at_least']} for r in rows],indent=2))
