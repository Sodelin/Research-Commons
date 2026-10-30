import argparse, hashlib, json
from pathlib import Path
parser=argparse.ArgumentParser(description="Extract exact coefficients from hash-verified inherited source banks.")
parser.add_argument("source_root",type=Path,help="Directory containing fullcap-normal and biased-joint-normal")
args=parser.parse_args()
p=args.source_root
root=Path(__file__).resolve().parent
manifest=json.loads((root/'SOURCE-BINDINGS.json').read_text())
for item in manifest['inputs']:
    data=(p/item['path']).read_bytes()
    actual=hashlib.sha256(data).hexdigest()
    if actual!=item['sha256']:
        raise SystemExit("SOURCE HASH MISMATCH: "+item['path'])
print("PASS: all four inherited input hashes",flush=True)
import sympy as s
q,x,b=s.symbols('q x beta');loc={'q':q,'x':x,'beta':b};a=json.load(open(p/'fullcap-normal/BARE-SOURCE-POLYNOMIAL.json'));n=json.load(open(p/'fullcap-normal/NORMAL-POLYNOMIAL.json'));N4=[s.sympify(v,locals=loc) for v in n['normal']];F4=[sum(s.Rational(rows[k][col])*q**int(e)*b**k for e,rows in a['bank'].items() for k in range(len(rows))) for col in n['selected_columns']]
a=json.load(open(p/'biased-joint-normal/DROP5-NORMAL.json'));N5=[-s.sympify(v,locals=loc) for v in a['normal']];F5=[s.sympify(v,locals=loc) for v in a['projected_source_polynomials']]
res={}
for label,N,F in [('f4',N4,F4),('f5',N5,F5)]:
 out={}
 for k in [0,1,2,3]:
  pol=s.factor(sum(n*s.diff(f,q,k).subs(q,1)*(-1)**k/s.factorial(k) for n,f in zip(N,F)))
  if pol==0:out[str(k)]={'polynomial':'0'};continue
  for j in range(12):
   v=s.factor(s.diff(pol,x,j).subs(x,1)*(-1)**j/s.factorial(j))
   if v!=0:break
  out[str(k)]={'polynomial':str(pol),'x_weak_order':j,'x_weak_coefficient':str(v)}
  print(label,k,j,v,flush=True)
 res[label]=out
json.dump(res,open(root/'coefficients.json','w'),indent=2)
