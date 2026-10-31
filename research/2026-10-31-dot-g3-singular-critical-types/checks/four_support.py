import sympy as s,itertools,json
L=[1,3,6,10,15,21]; qs=[s.Rational(1,2),s.Rational(1,3),s.Rational(1,4)]
results=[]
for J in itertools.combinations(L,4):
 annih=[]; data=[]
 for q in qs:
  M=s.Matrix([J,[1-q**l for l in J],[l*q**(l-1) for l in J]])
  ns=M.nullspace(); assert len(ns)==1
  d=ns[0]; V=s.Matrix.hstack(d,s.diag(*[q**l for l in J])*d)
  assert V.rank()==2
  rows=[v.T for v in V.T.nullspace()]
  annih.extend(rows)
  data.append({'q':str(q),'d':[str(x) for x in d],'annihilator_rows':[[str(x) for x in row] for row in rows]})
 A=s.Matrix.vstack(*annih); rank=A.rank()
 chosen=[]
 for i in range(A.rows):
  if A[chosen+[i],:].rank()>len(chosen): chosen.append(i)
  if len(chosen)==4: break
 minor=A[chosen,:].det()
 assert minor!=0
 results.append({'support':J,'slice_data':data,'stack_rank':rank,'intersection_dimension':4-rank,'selected_row_indices':chosen,'nonzero_minor':str(minor)})
print(json.dumps(results,indent=2))
assert all(x['stack_rank']==4 for x in results)
