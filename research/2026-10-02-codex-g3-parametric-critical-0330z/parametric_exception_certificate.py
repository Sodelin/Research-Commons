"""Explicit finite-exception polynomial via a 9x9 Sylvester determinant.

The characteristic-zero polynomial is defined by integer determinant formulas;
this bounded exact finite-field evaluation proves it is nonzero. Analytic and
Baker/source transfers are hand arguments in the companion note.
"""
from pathlib import Path
import hashlib, json, platform, resource, time
import sympy as S
resource.setrlimit(resource.RLIMIT_AS,(600*1024**2,600*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(20,20))
t0=time.monotonic()
lam=[1,3,6,10,15,21]
prime=1009
rmod=285
p=S.symbols('p')


def det_mod(a):
    a=[[int(x)%prime for x in row] for row in a]
    n=len(a); det=1
    for k in range(n):
        pivot=next((i for i in range(k,n) if a[i][k]),None)
        if pivot is None:return 0
        if pivot!=k:a[k],a[pivot]=a[pivot],a[k];det=-det
        d=a[k][k];det=det*d%prime
        inv=pow(d,-1,prime)
        for i in range(k+1,n):
            z=a[i][k]*inv%prime
            a[i]=[(x-z*y)%prime for x,y in zip(a[i],a[k])]
    return det%prime


def normal_matrix(r):
    rows=[[1]*6,lam[:]]
    for node in [r,r*r%prime]:
        rows += [[(1-pow(node,l,prime))%prime for l in lam],
                 [(l*pow(node,l-1,prime))%prime for l in lam]]
    return rows

M=normal_matrix(rmod)
D=det_mod(M)
C=[]
for i in range(6):
    sub=[row[:i]+row[i+1:] for row in M[1:]]
    C.append(((-1)**i*det_mod(sub))%prime)
assert D!=0 and sum(C)%prime==D
assert all(sum(x*y for x,y in zip(row,C))%prime==val
           for row,val in zip(M,[D,0,0,0,0,0]))
q0=3
f=[S.Poly(1-p+p*pow(q0,l,prime),p,modulus=prime) for l in lam]
P=S.Poly(0,p,modulus=prime);Q0=P
for i,l in enumerate(lam):
    other=S.Poly(1,p,modulus=prime)
    for j in range(6):
        if i!=j:other*=f[j]
    P += other.mul_ground(C[i]*(1-pow(q0,l,prime)))
    Q0 += other.mul_ground(C[i]*l*pow(q0,l-1,prime))
# The q-endpoint factors at q0=3 are nonzero scalar units; retain them.
Q=Q0.exquo(S.Poly(1-p,p,modulus=prime))
assert P.degree()==5 and Q.degree()==4
pc=[int(x)%prime for x in P.all_coeffs()]
qc=[int(x)%prime for x in Q.all_coeffs()]
Syl=[]
for shift in range(4):Syl.append([0]*shift+pc+[0]*(3-shift))
for shift in range(5):Syl.append([0]*shift+qc+[0]*(4-shift))
value=det_mod(Syl)
res=int(S.resultant(P,Q))%prime
print("pilot", value, res)
assert value==res and value!=0
# max distinct-column allocation for the four nonconstant normal rows.
import itertools
row_weights=[1,1,2,2]
max_degree=max(sum(w*lam[i] for w,i in zip(row_weights,perm))-3
               for perm in itertools.permutations(range(6),4))
assert max_degree==85
# Every Sylvester term contains four P coefficients and five Q coefficients.
exception_degree_bound=9*max_degree
record={
    'status':'PASS exact modular nonzero evaluation of explicit integer polynomial E(r)',
    'definition':{'lambda':lam,'normal_rows':['1','lambda','1-r^lambda','lambda*r^(lambda-1)',
        '1-r^(2*lambda)','lambda*r^(2*lambda-2)'],
        'D':'det M(r)','C_i':'(-1)^i det(M(r) with row 0 and column i deleted); i=0,...,5',
        'f_i_at_q3':'1-p+p*3^lambda_i',
        'P_at_q3':'sum_i C_i(r)*(1-3^lambda_i)*product_(j!=i) f_j',
        'Q_at_q3':'[sum_i C_i(r)*lambda_i*3^(lambda_i-1)*product_(j!=i) f_j]/(1-p)',
        'E':'Sylvester determinant Res_p(P_at_q3,Q_at_q3), padded degrees 5 and 4'},
    'prime':prime,'r_mod':rmod,'normal_matrix_mod':M,'D_mod':D,'C_mod':C,
    'normal_mod':[(x*pow(D,-1,prime))%prime for x in C],
    'P_coefficients_descending_mod':pc,'Q_coefficients_descending_mod':qc,
    'Sylvester_matrix_mod':Syl,'E_mod':value,
    'independent_sympy_resultant_mod':res,
    'normal_cofactor_degree_bound':max_degree,
    'exception_polynomial_degree_bound':exception_degree_bound,
    'P_p_degree':int(P.degree()),'Q_p_degree':int(Q.degree()),
    'python':platform.python_version(),'sympy':S.__version__,'seconds':time.monotonic()-t0,
    'scope':'One exact evaluation certifies E is nonzero as an integer polynomial. The finite-exception theorem, no strict vertical curves, isolated point algebraicity, Baker rationality and source transfer are separately proved by hand. No E expansion, root isolation or general recognizer.'}
record['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
Path(__file__).with_name('parametric-exception-certificate.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['status','D_mod','C_mod','E_mod','exception_polynomial_degree_bound','seconds']}))
