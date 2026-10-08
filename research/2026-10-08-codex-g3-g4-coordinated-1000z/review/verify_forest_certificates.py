from pathlib import Path
from fractions import Fraction as F
from math import comb,factorial
from collections import Counter
import ast,json,hashlib,datetime
BASE=Path('/workspace/Research-Commons/research/2026-10-08-codex-g3-g4-coordinated-1000z')
L=json.loads((BASE/'g4-forest/EXACT-CUBIC-LAYER-v2.json').read_text())
J=json.loads((BASE/'g4-forest/ACTUAL-BANK-JACOBIAN-v2.json').read_text())
def rational_matrix(a):return [[F(x) for x in row] for row in a]
def rref(a,p=None):
 a=[r[:] for r in a];k=0;piv=[];labels=list(range(len(a)));rows=[]
 for j in range(len(a[0])):
  i=next((i for i in range(k,len(a)) if a[i][j]),None)
  if i is None:continue
  a[k],a[i]=a[i],a[k];labels[k],labels[i]=labels[i],labels[k]
  d=a[k][j];inv=pow(d,-1,p) if p else 1/d
  a[k]=[(v*inv)%p if p else v*inv for v in a[k]]
  for i in range(len(a)):
   if i!=k and a[i][j]:
    d=a[i][j];a[i]=[(v-d*w)%p if p else v-d*w for v,w in zip(a[i],a[k])]
  piv.append(j);rows.append(labels[k]);k+=1
  if k==len(a):break
 return a[:k],rows,piv
def determinant(a,p):
 a=[r[:] for r in a];v=1
 for k in range(len(a)):
  i=next((i for i in range(k,len(a)) if a[i][k]),None)
  if i is None:return 0
  if i!=k:a[k],a[i]=a[i],a[k];v=-v
  d=a[k][k];v=v*d%p;inv=pow(d,-1,p)
  for i in range(k+1,len(a)):
   scale=a[i][k]*inv%p
   a[i]=[(x-scale*y)%p for x,y in zip(a[i],a[k])]
 return v%p
def mm(a,b):return [[sum((x*y for x,y in zip(r,c)),F(0)) for c in zip(*b)] for r in a]
def size(t):return 1 if not t else size(t[0])+size(t[1])
def key(t):return size(t),repr(t)
def join(a,b):return tuple(sorted((a,b),key=key))
def forest(ts):return tuple(sorted(ts,key=key))
def automorphism(t):return 1 if not t else automorphism(t[0])*automorphism(t[1])*(2 if t[0]==t[1] else 1)
states=list(map(ast.literal_eval,L['shape_order']));index={s:i for i,s in enumerate(states)}
Q=rational_matrix(L['ordinary_Q']);R=rational_matrix(L['actual_cubic_R']);expected=[]
for s in states:
 n=len(s);row=[F(0)]*20;row[index[s]]=-F(3,2)*comb(n,3)
 for a,b in __import__('itertools').combinations(range(n),2):
  out=forest([t for i,t in enumerate(s) if i not in (a,b)]+[join(s[a],s[b])]);row[index[out]]+=F(3,4)*(n-2)
 for a,b,c in __import__('itertools').combinations(range(n),3):
  for u,v,w in [(a,b,c),(a,c,b),(b,c,a)]:
   out=forest([t for i,t in enumerate(s) if i not in (a,b,c)]+[join(join(s[u],s[v]),s[w])]);row[index[out]]-=F(1,4)
 expected.append(row)
assert expected==R
assert all(sum(row)==0 for row in Q+R)
assert all(Q[i][i]==-comb(len(s),2) for i,s in enumerate(states))
orbits=[]
for s in states:
 den=1
 for t in s:den*=automorphism(t)
 for v in Counter(s).values():den*=factorial(v)
 orbits.append(factorial(6)//den)
assert orbits==L['labelled_orbit_sizes']
coef=rational_matrix(L['moment_coefficient_matrix']);C=rational_matrix(L['delete_one_C'])
assert all(sum(col)==6 for col in zip(*C))
assert len(rref(C)[2])==10
constraints=mm(C,coef)+[coef[0]]
assert constraints==rational_matrix(L['all_lower_plus_diagonal_constraints'])
assert rref(constraints)[0]==rational_matrix(L['constraint_rref'])
assert [len(rref(a)[2]) for a in [coef,constraints,rational_matrix(L['constrained_full_residual_columns']),rational_matrix(L['constrained_nine_columns'])]]==[9,6,3,3]
assert mm(constraints,[list(c) for c in zip(*rational_matrix(L['moment_fibre_basis']))])==[[F(0)]*3 for _ in constraints]
P=J['prime'];full=J['full_20_by_36_jacobian_mod_prime'];lower=J['complete_lower_plus_new_diagonal_jacobian_mod_prime']
rr,cc=J['full_minor_rows'],J['full_minor_columns'];det=determinant([[full[i][j] for j in cc] for i in rr],P)
assert det==J['full_minor_determinant_mod_prime'] and det!=0
assert len(rref(full,P)[2])==18 and len(rref(lower,P)[2])==9
lr,lc=rref(lower,P)[1:];ldet=determinant([[lower[i][j] for j in lc] for i in lr],P);assert ldet!=0
projection=mm(C,[[F(x) for x in row] for row in full])+[[F(x) for x in full[0]]]
assert [[int(x)%P for x in row] for row in projection]==lower
pair=list(map(F,J['six_root_pair_survival_functional']))
assert pair==[1-F(sum(comb(size(t),2) for t in s),15) for s in states]
def mod(x):return x.numerator*pow(x.denominator,-1,P)%P
assert all(sum(col)%P==0 and sum(mod(x)*v for x,v in zip(pair,col))%P==0 for col in zip(*full))
assert J['base_response_mod_prime']!=J['ordinary_target_mod_prime']
result={'schema':'independent-static-arithmetic-certificate-review-v1','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'executed_review_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'scope':'JSON certificate arithmetic only; no source/helper/scientific module execution, compiler, QE, Newton or source solver','inputs':[{'path':str(BASE/'g4-forest'/name),'sha256':hashlib.sha256((BASE/'g4-forest'/name).read_bytes()).hexdigest()} for name in ['EXACT-CUBIC-LAYER-v2.json','ACTUAL-BANK-JACOBIAN-v2.json']],'universal_current_root_cubic_operator_matches':True,'independent_orbit_counts':orbits,'rational_constraint_ranks':[9,6,3,3],'full_rank_mod_prime':18,'full_minor_determinant_mod_prime':det,'lower_plus_diagonal_rank_mod_prime':9,'independently_extracted_lower_minor_rows':lr,'independently_extracted_lower_minor_columns':lc,'independently_extracted_lower_minor_determinant_mod_prime':ldet,'nonordinary_base_modular_control':True,'mass_pair_constraints_and_lower_projection_match':True,'status':'PASS_STATIC_CERTIFICATE_ARITHMETIC_ONLY'}
out=BASE/'review/G4-FOREST-STATIC-CERTIFICATE-VERIFICATION.json';out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','full_minor_determinant_mod_prime','independently_extracted_lower_minor_determinant_mod_prime']}))
