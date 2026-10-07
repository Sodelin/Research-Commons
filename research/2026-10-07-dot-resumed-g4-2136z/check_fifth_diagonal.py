"""Bounded exact algebra only. No source generation, parameter scan, or compiler."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import hashlib, json

HERE=Path(__file__).resolve().parent
raw=(HERE/"FROZEN-FIFTH-SOURCE-RESULT.json").read_bytes()
EXPECTED="0a71280a0a41c3e39204f06400d4c56ba6e8e408f2f4a8015769256435646d8b"
assert hashlib.sha256(raw).hexdigest()==EXPECTED
R=json.loads(raw)
indices={n: next(i for i,x in enumerate(R["complete_coordinates"])
                  if x["arity"]==n and x["shape"]==["x"]*n)
         for n in (2,3,4,5)}
def phi(v):
    return F(v[indices[5]])-5*F(v[indices[4]])+10*F(v[indices[3]])-6*F(v[indices[2]])
assert all(phi(v)==0 for v in R["lower_operators"].values())
arrays={(x["rho_degree"],x["z_degree"]):x["values"] for x in R["fifth_coefficient_arrays"]}
for row in R["actual_source_quotient_polynomial"]:
    A,B=map(F,row["quotient_coefficients"])
    assert phi(arrays[row["rho_degree"],row["z_degree"]])==24*(A-5*B)

# Exact univariate polynomial arithmetic in d, with fractions. No CAS required.
def add(*ps):
    out=[F(0)]*max(map(len,ps))
    for p in ps:
        for i,x in enumerate(p):out[i]+=x
    while len(out)>1 and out[-1]==0:out.pop()
    return out
def scale(p,c):return [c*x for x in p]
def mul(p,q):
    out=[F(0)]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):out[i+j]+=x*y
    return out
def power(p,n):
    out=[F(1)]
    for _ in range(n):out=mul(out,p)
    return out
def monomial(n,c=F(1)):return [F(0)]*n+[F(c)]

# Extract H directly from EVERY authenticated actual source coefficient row.
# Substitute rho=1-d and z=t+d; retain polynomial coefficients in t.
Ht=[[F(0)] for _ in range(5)]
for row in R["actual_source_quotient_polynomial"]:
    a,b=row["rho_degree"],row["z_degree"]
    A,B=map(F,row["quotient_coefficients"]);c=A-5*B
    for j in range(b+1):
        Ht[j]=add(Ht[j],scale(mul(power([F(1),F(-1)],a),
                                     monomial(b-j)),c*comb(b,j)))

expected=[
    scale(mul(monomial(5),[F(-12),F(85),F(-100),F(45),F(-10),F(1)]),F(1,24)),
    scale(mul(monomial(4),[F(6),F(-6),F(1)]),F(5,6)),
    scale(mul(monomial(2),[F(-2),F(3)]),F(-5,4)),
    monomial(1,F(-5,2)),[F(5,24)]]
assert Ht==expected
mu1=[F(0),F(-1,8),F(-11,20),F(11,120)]
mu2=monomial(3,F(1,3))
k0=add(monomial(5,F(1,15)),monomial(6,F(-1,90)))
mu3=add(mul(monomial(3),mu1),scale(k0,F(6)))
const=add(Ht[0],mul(Ht[1],mu1),mul(Ht[2],mu2),mul(Ht[3],mu3))
P=list(map(F,[3,78,-162,138,-49,6]))
assert const==scale(mul(monomial(5),P),F(1,144))
bernstein=[sum(P[i]*F(comb(k,i),comb(5,i)) for i in range(k+1)) for k in range(6)]
assert bernstein==[F(3),F(93,5),F(18),F(15),F(68,5),F(14)]
assert min(bernstein)==3
def evaluate(p,x):return sum(v*x**i for i,v in enumerate(p))
assert evaluate(const,F(1,4))==F(7345,75497472)
report={
 "status":"PASS exact coefficient identities only",
 "source_sha256":EXPECTED,
 "source_bytes":len(raw),
 "all_saved_fifth_monomials_checked":len(R["actual_source_quotient_polynomial"]),
 "all_saved_lower_operators_annihilated":list(R["lower_operators"]),
 "diagonal_coordinate_indices":indices,
 "phi_basis_values":["24","-120"],
 "H_in_t_coefficients":[list(map(str,p)) for p in Ht],
 "mean_H_constant_coefficients":list(map(str,const)),
 "P_power_coefficients":list(map(str,P)),
 "P_Bernstein_coefficients":list(map(str,bernstein)),
 "rho_three_quarters_mean_constant":str(evaluate(const,F(1,4))),
 "source_expansion_run":False,"parameter_search":False,"compiler_run":False,
 "semantic_proof_independently_reviewed":False,
 "original_G4_closed":False}
print(json.dumps(report,indent=2,sort_keys=True))

