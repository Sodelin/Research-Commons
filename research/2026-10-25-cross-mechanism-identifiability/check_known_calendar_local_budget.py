"""Exact two-epoch local conditioning/budget certificate, not data fitting."""
from fractions import Fraction as F
from math import factorial
import json
# Center hazards (1,1), known cut log(2), s=1, mu=3/8.
J=[[F(3,16),F(1,16)],[F(7,36),F(1,36)]]
A=[[-4,9],[28,-27]]
assert all(sum(A[i][k]*J[k][j] for k in range(2))==int(i==j) for i in range(2) for j in range(2))
B=max(sum(abs(v) for v in r) for r in A);assert B==55
b=F(1,512);floor=F(1,2)
H=max(F(2*r,1)/(F(r)+floor)**3 for r in [1,2]);assert H==F(16,27)
kappa=B*4*H*b;assert kappa==F(55,216) and kappa<1
c=(1-kappa)/B;eta=b;Delta=c*eta;eps=Delta/3
# log(2m/delta)=log(80)<5, certified by a positive Taylor lower bound.
exp5_lower=sum(F(5**k,factorial(k)) for k in range(7));assert exp5_lower>80
required=10/eps**2;N=(required.numerator+required.denominator-1)//required.denominator
assert F(N)*eps**2/2>=5
out={'status':'exact local algebra/budget checks passed','epochs':2,'known_calendar_cut':'log(2)','known_JC_mu':'3/8','center_hazards':['1','1'],'hazard_box':[str(1-b),str(1+b)],'jacobian':[[str(x) for x in r] for r in J],'inverse_jacobian':A,'inverse_infinity_norm':B,'H_max_upper_bound':str(H),'kappa_upper_bound':str(kappa),'inverse_separation_slope':str(c),'hazard_resolution_eta':str(eta),'certified_moment_separation':str(Delta),'moment_radius_epsilon':str(eps),'confidence_error_delta':'1/20','independent_loci_budget':N,'sites_per_locus':2,'copies_per_site':2,'nucleotide_calls':4*N,'interpretation':'Conservative mathematical certificate is extremely large; no practical adequacy, biological fit, simulation, or complete confidence-set engine is claimed.'}
print(json.dumps(out,indent=2))
