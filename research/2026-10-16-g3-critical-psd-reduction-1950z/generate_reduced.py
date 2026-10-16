"""Own exact serializer/static arithmetic checks; never invokes an SMT solver."""
import json, hashlib, re
from pathlib import Path
from fractions import Fraction as F
import sympy as S
HERE=Path(__file__).resolve().parent
raw=(HERE/'normal-source.json').read_bytes(); obj=json.loads(raw)
ls=obj['lambda']; assert ls==[1,3,6,10,15,21]
cs=[[int(x) for x in row] for row in obj['B_coefficients_descending']]
assert [len(x)-1 for x in cs]==obj['B_degrees']
def num(n): return str(n) if n>=0 else f'(- {-n})'
def add(xs): return '(+ '+' '.join(xs)+')'
def mul(xs): return '(* '+' '.join(xs)+')'
def power(x,n):
    if n==0:return '1'
    if n==1:return x
    return f'(^ {x} {n})'
def horner(row):
    z=num(row[0])
    for a in row[1:]:z=f'(+ (* {z} r) {num(a)})'
    return z
lines=['; Own reduced query, 2026-10-16. UNEXECUTED by any SMT solver.',
'; Exactly three real variables; source cofactor arrays retained with hashes.',
'(set-logic QF_NRA)','(set-option :produce-models true)']
lines += [f'(declare-const {x} Real)' for x in ['r','p','q']]
lines += ['(assert (and (> r 0) (< r 1) (> p 0) (< p 1) (> q 0) (< q 1)))']
def define(n,e):lines.append(f'(define-fun {n} () Real {e})')
for i,row in enumerate(cs):define(f'b{i}',horner(row))
define('d',add([f'b{i}' for i in range(6)]))
for i,l in enumerate(ls):define(f'f{i}',f'(+ (- 1 p) (* p {power("q",l)}))')
define('Fprod',mul([f'f{i}' for i in range(6)]));define('U','(* Fprod Fprod)')
for i in range(6):
 define(f'v{i}',mul([f'f{j}' for j in range(6) if j!=i]));define(f'u{i}',f'(* v{i} v{i})')
define('P0',add([f'(* b{i} (- 1 {power("q",l)}) v{i})' for i,l in enumerate(ls)]))
define('Q0',add([f'(* {l} b{i} {power("q",l-1)} v{i})' for i,l in enumerate(ls)]))
define('T0',f'(* d (- {add([f"(* b{i} u{i})" for i in range(6)])} (* d U)))')
for k in [1,2]:define(f'T{k}',f'(* d {add([f"(* {l**k} b{i} {power(chr(113),l)} u{i})" for i,l in enumerate(ls)])})')
define('detScaled','(- (* (- 1 p) (- T0) T2) (* p T1 T1))')
lines+=['(assert (= P0 0))','(assert (= Q0 0))','(assert (>= T0 0))','(assert (<= T2 0))','(assert (>= detScaled 0))','(check-sat)']
query='\n'.join(lines)+'\n'; (HERE/'QUERY-REDUCED-UNEXECUTED.smt2').write_text(query)
# Parse the generated text ourselves to verify balanced complete forms and evaluate definitions.
tokens=re.findall(r'\(|\)|[^\s()]+', re.sub(r';[^\n]*','',query)); pos=0
def parse():
 global pos
 t=tokens[pos];pos+=1
 if t!='(': assert t!=')'; return t
 out=[]
 while tokens[pos]!=')':out.append(parse())
 pos+=1;return out
forms=[]
while pos<len(tokens):forms.append(parse())
assert [x[1] for x in forms if x[0]=='declare-const']==['r','p','q']
assert forms[-1]==['check-sat']
def ev(x,env):
 if isinstance(x,str):return env[x] if x in env else F(x)
 op=x[0];a=[ev(z,env) for z in x[1:]]
 if op=='+':return sum(a,F(0))
 if op=='*':
  z=F(1)
  for v in a:z*=v
  return z
 if op=='-':return -a[0] if len(a)==1 else a[0]-a[1]
 if op=='^':assert a[1].denominator==1;return a[0]**int(a[1])
 raise ValueError(op)
r=S.Symbol('r');bs=[S.Poly.from_list(row,r).as_expr() for row in cs]
normal_rows=[[l for l in ls],[1-r**l for l in ls],[l*r**(l-1) for l in ls],[1-r**(2*l) for l in ls],[l*r**(2*l-2) for l in ls]]
assert all(S.Poly(sum(b*a for b,a in zip(bs,row)),r).is_zero for row in normal_rows)
points=[(F(1,2),F(1,3),F(2,3)),(F(1,3),F(3,4),F(1,4)),(F(2,3),F(1,5),F(3,5))]
for rr,pp,qq in points:
 env=dict(r=rr,p=pp,q=qq)
 for form in forms:
  if form[0]=='define-fun':env[form[1]]=ev(form[4],env)
 d=env['d'];assert d!=0
 c=[env[f'b{i}']/d for i in range(6)];fs=[env[f'f{i}'] for i in range(6)]
 assert sum(c)==1 and min(fs)>0
 lp=sum(ci*(1-qq**l)/f for ci,l,f in zip(c,ls,fs))
 lq=-sum(ci*pp*l*qq**(l-1)/f for ci,l,f in zip(c,ls,fs))
 ss=[sum(ci/f**2 for ci,f in zip(c,fs))-1]+[sum(l**k*ci*qq**l/f**2 for ci,l,f in zip(c,ls,fs)) for k in [1,2]]
 assert env['P0']==d*env['Fprod']*lp
 assert env['Q0']==-d*env['Fprod']*lq/pp
 for k in range(3):assert env[f'T{k}']==d*d*env['U']*ss[k]
 aa=sum(ci*(1-qq**l)**2/f**2 for ci,l,f in zip(c,ls,fs))
 bb=-sum(ci*l*qq**(l-1)/f**2 for ci,l,f in zip(c,ls,fs))
 cc=sum(ci*(-pp*l*(l-1)*qq**(l-2)/f+pp**2*l*l*qq**(2*l-2)/f**2) for ci,l,f in zip(c,ls,fs))
 assert aa==ss[0]/pp**2-2*lp/pp and bb==-ss[1]/qq
 assert qq**2*cc==-pp*(1-pp)*ss[2]-qq*lq
 assert env['detScaled']==(d*d*env['U'])**2*(-(1-pp)*ss[0]*ss[2]-pp*ss[1]**2)
record={'status':'PASS serialization, exact normal polynomial identities, three rational arithmetic controls','solver_executed':False,'global_query_result':'UNEXECUTED','source_json_sha256':hashlib.sha256(raw).hexdigest(),'query_sha256':hashlib.sha256(query.encode()).hexdigest(),'own_generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'sympy_version':S.__version__,'checks':['exact normal identities, no cofactor recomputation','parsed exactly three declared real variables','three rational evaluations of cleared gradients and scaled Hessian identities including off-critical residual terms'],'scope':'Own finite static/arithmetic controls; not SMT syntax-parser acceptance or global sign proof.'}
(HERE/'STATIC-CHECKS.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
