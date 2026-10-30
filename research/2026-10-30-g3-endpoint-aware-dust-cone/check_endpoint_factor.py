import argparse,hashlib,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('source_root',type=Path);args=ap.parse_args()
root=Path(__file__).resolve().parent
manifest=json.loads((root/'SOURCE-BINDINGS.json').read_text())
for item in manifest['inputs']:
 data=(args.source_root/item['path']).read_bytes()
 if hashlib.sha256(data).hexdigest()!=item['sha256']:
  raise SystemExit('SOURCE HASH MISMATCH: '+item['path'])
print('PASS: all four input hashes before SymPy extraction',flush=True)
p=args.source_root/'biased-joint-normal/DROP5-NORMAL.json' 
assert hashlib.sha256(p.read_bytes()).hexdigest()=='f41e156baab248bdc2306c4a49a7d9f7b9abe6bd4f9b5ca7f00e34cc4be9ad19'
import sympy as s
q,x,b=s.symbols('q x beta');loc={'q':q,'x':x,'beta':b}
a=json.loads(p.read_text());N=[-s.sympify(v,locals=loc) for v in a['normal']];F=[s.sympify(v,locals=loc) for v in a['projected_source_polynomials']]
factor=(1-b)*(1-q)**2
G=[]
for f in F:
 quo,rem=s.div(f,factor,q,b)
 assert s.expand(rem)==0
 assert s.expand(f-factor*quo)==0
 G.append(quo)
C=s.factor(sum(n*(-s.diff(f,q,3).subs({q:1,b:0}))/6 for n,f in zip(N,F)))
H0=s.factor(sum(n*g.subs(q,1) for n,g in zip(N,G)))
assert s.factor(H0+6*b*C)==0
for g in G:
 quo,rem=s.div(g-g.subs(q,1),1-q,q,b)
 assert s.expand(rem)==0
# Independently check the same exact factor and boundary tie for f4.
p4=args.source_root/'fullcap-normal/BARE-SOURCE-POLYNOMIAL.json'
n4=args.source_root/'fullcap-normal/NORMAL-POLYNOMIAL.json'
assert hashlib.sha256(p4.read_bytes()).hexdigest()=='7a11564ca02d2a6c5d036318758ec214dbe4fdcd03a9cba94ad3a6ed8575cea2'
assert hashlib.sha256(n4.read_bytes()).hexdigest()=='2844871e9c48a810df35670da4b5eb1f8c02c564d0c5bf3a13e43c141c097a3a'
a4=json.loads(p4.read_text());n4j=json.loads(n4.read_text())
N4=[s.sympify(v,locals=loc) for v in n4j['normal']]
F4=[sum(s.Rational(rows[k][col])*q**int(e)*b**k for e,rows in a4['bank'].items() for k in range(len(rows))) for col in n4j['selected_columns']]
G4=[]
for f in F4:
 quo,rem=s.div(f,factor,q,b)
 assert s.expand(rem)==0
 G4.append(quo)
C4=s.factor(sum(n*(-s.diff(f,q,3).subs({q:1,b:0}))/6 for n,f in zip(N4,F4)))
H04=s.factor(sum(n*g.subs(q,1) for n,g in zip(N4,G4)))
assert s.factor(H04+6*b*C4)==0
assert s.cancel(C/(1-x)**5).subs(x,1)==-s.Rational(21271359375,4)
assert s.cancel(C4/(1-x)**3).subs(x,1)==s.Rational(275625,176)
out={'weak_reference_coefficients':'PASS','status':'PASS' ,'f4_factor_and_boundary_tie':'PASS','f4_projected_polynomials':len(F4),'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'projected_polynomials':len(F),'exact_factor':'(1-beta)*(1-q)^2','normalized_identity':'f_j=(1-beta)*a^2*(-6*beta*C_j(x)+a*D_j(a,beta,x)), j=4,5; a=1-q; D_j polynomial','checks':['Each projected source polynomial divisible by exact factor','f5 uses minus saved raw normal','Normalized q=1 coefficient equals -6*beta*C5(x) identically','Remaining normalized polynomial divisible by 1-q'],'scope':'Exact polynomial identity; no complete-return or uniform x-to-one claim'}
Path(__file__).with_name('endpoint-factor-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
