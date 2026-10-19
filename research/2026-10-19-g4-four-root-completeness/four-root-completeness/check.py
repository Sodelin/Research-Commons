import sympy as s
from functools import lru_cache
from itertools import combinations

def canon(a,b):return tuple(sorted((a,b),key=str))
def forest(ts):return tuple(sorted(ts,key=str))
def shape(t):return 'L' if isinstance(t,int) else '('+''.join(sorted(map(shape,t)))+')'
@lru_cache(None)
def states(n):
 start=tuple(range(n));seen={start};todo=[start]
 while todo:
  f=todo.pop()
  for i,j in combinations(range(len(f)),2):
   g=forest([t for k,t in enumerate(f) if k not in (i,j)]+[canon(f[i],f[j])])
   if g not in seen:seen.add(g);todo.append(g)
 return tuple(sorted(seen,key=lambda f:(-len(f),str(f))))
def prune(t,keep):
 if isinstance(t,int):return t if t in keep else None
 a,b=map(lambda t:prune(t,keep),t)
 return b if a is None else a if b is None else canon(a,b)
def restrict(f,keep):return forest([r for t in f if (r:=prune(t,keep)) is not None])
def orbit(f):return tuple(sorted(map(shape,f)))
ss=states(4);orbs=sorted(set(map(orbit,ss)));print(len(ss),orbs)
cols=[]
for o in orbs:
 fs=[f for f in ss if orbit(f)==o]
 vals=[1,s.Rational(sum(len(restrict(f,{0,1}))==2 for f in fs),len(fs)),s.Rational(sum(len(restrict(f,{0,1,2}))==3 for f in fs),len(fs)),int(o==('L','L','L','L'))]
 # c4=(P31-2P22)/10
 vals.append(s.Rational(1,10) if o==('((LL)L)','L') else -s.Rational(1,5) if o==('(LL)','(LL)') else 0)
 cols.append(vals)
M=s.Matrix.hstack(*map(s.Matrix,cols));print(M);print('rank',M.rank(),'null',M.nullspace())
assert len(ss)==37 and len(orbs)==6
assert M.rank()==5 and M.nullspace()==[s.Matrix([-1,1,0,0,0,0])]
# Extra row balanced minus total one-root probability /3.
extra=s.Matrix([[-s.Rational(1,3),s.Rational(2,3),0,0,0,0]])
assert M.col_join(extra).rank()==6
cA,cB,bA,bB,dA,z=s.symbols('cA cB bA bB dA z')
c_after=cA*z*bB+dA*z**6*cB
e_after=-s.Rational(10,3)*cA*(1-z)-s.Rational(10,3)*cA*z*(1-bB)
assert s.expand(e_after+s.Rational(10,3)*cA*(1-z*bB))==0
print('PASS: complete orbit basis needs extra balanced-versus-comb row; exact two-cell extra-row identity')
