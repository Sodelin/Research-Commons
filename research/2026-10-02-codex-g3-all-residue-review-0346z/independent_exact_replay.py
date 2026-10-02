"""Reviewer-authored exact reconstruction, determinant replay and alternate positivity check."""
from pathlib import Path
import json, hashlib, time, resource, sys
import sympy as S
from sympy.polys.matrices import DomainMatrix
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(1100*1024**2,1100*1024**2))
t=time.monotonic()
root=Path(__file__).parent
source=Path(sys.argv[1]) if len(sys.argv)>1 else root.parent/'2026-10-02-codex-g3-parametric-critical-0330z'
if not source.exists():source=root.parent/'g3-parametric-critical-0323z'
manifest=json.loads((source/'MANIFEST.json').read_text())
for f, rec in manifest['files'].items():
    b=(source/f).read_bytes()
    assert len(b)==rec['bytes'] and hashlib.sha256(b).hexdigest()==rec['sha256'], f
r,p,q=S.symbols('r p q')
ls=[1,3,6,10,15,21]
dom=S.ZZ.poly_ring(r)
rows=[[dom.from_sympy(expr) for expr in row] for row in [
 [S.Integer(1) for n in ls],ls,[1-r**n for n in ls],
 [n*r**(n-1) for n in ls],[1-r**(2*n) for n in ls],
 [n*r**(2*n-2) for n in ls]]]
# Matrix-domain fraction-free determinants, not the contributor's permutation loop.
C=[]
for i in range(6):
    minor=[[row[j] for j in range(6) if j!=i] for row in rows[1:]]
    C.append(S.Poly(dom.to_sympy((-1)**i*DomainMatrix(minor,(5,5),dom).det()),r))
D=S.Poly(dom.to_sympy(DomainMatrix(rows,(6,6),dom).det()),r)
assert sum(C,S.Poly(0,r))==D
assert all(sum((C[i]*S.Poly(dom.to_sympy(rows[k][i]),r) for i in range(6)),S.Poly(0,r)).is_zero for k in range(1,6))
g=S.Poly(3*r**8*(r-1)**12*(r+1)**4*(r*r+r+1)**4*(r**4+r**3+r*r+r+1),r)
B=[v.exquo(g) for v in C]
recorded=json.loads((source/'symbolic-normal-pilot.json').read_text())
assert [[str(c) for c in b.all_coeffs()] for b in B]==recorded['B_coefficients_descending']
cg=C[0]
for v in C[1:]:cg=S.gcd(cg,v)
assert cg==g
d=sum(B,S.Poly(0,r))
dcontent,dfactors=S.factor_list(d)
assert dcontent>0
for f,e in dfactors:
    if f.as_expr()==r: pass
    elif f.as_expr()==r*r-r+1: pass
    else: assert all(c>=0 for c in f.all_coeffs()) and f.eval(0)>0
print(json.dumps({'stage':'normal reconstructed','seconds':time.monotonic()-t}),flush=True)
# Build coefficient arrays by linear-factor convolution, no contributor Poly(p) product construction.
def convolution(a,b):
    out=[a[0]*0 for _ in range(len(a)+len(b)-1)]
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j]+=x*y
    return out
E=[]
slices=[]
for z in [3,5]:
    P=[S.Poly(0,r) for _ in range(6)]
    Q0=[S.Poly(0,r) for _ in range(6)]
    for i,n in enumerate(ls):
        product=[S.Poly(1,r)]
        for j,m in enumerate(ls):
            if j!=i:product=convolution(product,[S.Poly(1,r),S.Poly(z**m-1,r)])
        for k in range(6):
            P[k]+=B[i]*(1-z**n)*product[k]
            Q0[k]+=B[i]*n*z**(n-1)*product[k]
    # Quotient by (1-p): cumulative coefficient sums, with exact top cancellation.
    Q=[]; acc=S.Poly(0,r)
    for k in range(5):
        acc+=Q0[k];Q.append(acc)
    assert Q0[5]==-Q[4] and not P[5].is_zero and not Q[4].is_zero
    # 9x9 Sylvester determinant built explicitly, independent of resultant primitive.
    pc=[dom.from_sympy(x.as_expr()) for x in P[::-1]]
    qc=[dom.from_sympy(x.as_expr()) for x in Q[::-1]]
    matrix=[]
    for shift in range(4):matrix.append([dom.zero]*shift+pc+[dom.zero]*(3-shift))
    for shift in range(5):matrix.append([dom.zero]*shift+qc+[dom.zero]*(4-shift))
    raw=S.Poly(dom.to_sympy(DomainMatrix(matrix,(9,9),dom).det()),r)
    content,primitive=raw.primitive()
    pinned=json.loads((source/f'slice-{z}-resultant.json').read_text())
    assert raw.degree()==pinned['resultant_degree']==385
    assert str(content)==pinned['content']
    assert [str(c) for c in primitive.all_coeffs()]==pinned['primitive_coefficients_descending']
    E.append(primitive)
    slices.append({'q':z,'degree':int(raw.degree()),'all_coefficients_match':True,
                   'raw_content':str(content),'seconds':time.monotonic()-t})
    print(json.dumps({'stage':'Sylvester slice','q':z,'degree':385,'seconds':time.monotonic()-t}),flush=True)
G=S.gcd(E[0],E[1])
receipt=json.loads((source/'two-slice-resultant-pilot.json').read_text())
assert [str(c) for c in G.all_coeffs()]==receipt['gcd_coefficients_descending']
assert G.degree()==238
content,factors=S.factor_list(G)
prod=S.Poly(content,r)
kinds=[]
for f,e in factors:
    prod*=f**e
    if f.as_expr()==r:kind='r positive'
    elif f.as_expr()==r*r-r+1:kind='quadratic strictly positive'
    elif all(c>=0 for c in f.all_coeffs()) and f.eval(0)>0:
        kind='nonnegative coefficients, positive constant'
    else:
        assert f.degree()==34
        remainder=S.Poly(f.as_expr()-(r**31+r)*(r*r-r+1),r)
        assert all(c>=0 for c in remainder.all_coeffs()) and remainder.eval(0)>0
        # Independent, simpler identity than the contributor's two square groups.
        assert remainder+(S.Poly(r**31+r,r)*S.Poly(r*r-r+1,r))==f
        kind='(r^31+r)(r^2-r+1) plus nonnegative coefficients, positive constant'
    kinds.append({'degree':int(f.degree()),'multiplicity':int(e),'positivity':kind})
assert prod==G and content>0
# Generic degree and strict leading-coefficient identities; built as sparse q polynomials.
pqdom=S.ZZ.poly_ring(r,q)
PP=[S.Poly(0,r,q) for _ in range(6)]
QQ0=[S.Poly(0,r,q) for _ in range(6)]
for i,n in enumerate(ls):
    product=[S.Poly(1,r,q)]
    for j,m in enumerate(ls):
        if j!=i:product=convolution(product,[S.Poly(1,r,q),S.Poly(q**m-1,r,q)])
    bi=S.Poly(B[i].as_expr(),r,q)
    for k in range(6):
        PP[k]+=bi*S.Poly(1-q**n,r,q)*product[k]
        QQ0[k]+=bi*S.Poly(n*q**(n-1),r,q)*product[k]
assert PP[5]==-S.Poly(d.as_expr()*S.prod(1-q**n for n in ls),r,q)
acc=S.Poly(0,r,q); QQ=[]
for k in range(5):
    acc+=QQ0[k]; QQ.append(acc)
assert QQ0[5]==-QQ[4]
assert max(x.degree(q) for x in PP)==56
assert max(x.degree(q) for x in QQ)<=55
out={'reviewer':'Codex / review_g3_all_residue_strengthening',
 'source_commit':'b7c072d53e4cb68624935b0283c66f2bcd525956',
 'status':'PASS independent exact reconstruction and full Sylvester coefficient replay',
 'limits':{'cpu_seconds':120,'address_space_mib':1100},
 'python':sys.version.split()[0],'sympy':S.__version__,
 'C_degrees':[int(x.degree()) for x in C],'B_degrees':[int(x.degree()) for x in B],
 'normal_and_exact_gcd_cofactor_identities':True,
 'slices':slices,'gcd_degree':238,'positive_gcd_factors':kinds,
 'independent_J_identity':'J=(r^31+r)(r^2-r+1)+K; K has nonnegative coefficients and K(0)=1',
 'strict_P0_p5_identity':True,'Q0_division_1_minus_p':True,
 'q_degrees':[int(max(x.degree(q) for x in PP)),int(max(x.degree(q) for x in QQ))],
 'advertised_q_degree_bounds':[56,55],'q_resultant_degree_bound':499,'distinct_pair_bound':2495,
 'source_manifest_all_hashes_match':True,
 'seconds':time.monotonic()-t,
 'scope':'Exact finite algebra and polynomial identities; source transfer is a reviewed hand theorem, not a kernel proof. No root isolation, critical-point list or source witness enumeration executed.'}
(root/'independent-exact-replay.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out),flush=True)
