from pathlib import Path
from fractions import Fraction as F
from itertools import combinations,product
import sys,json,hashlib
import sympy as s
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'disposable'))
from fourier_motzkin import project_open_cube

def frac(v):
 v=s.Rational(v);return F(int(v.p),int(v.q))
def solve(A,b):
 n=len(b);M=[list(a)+[c] for a,c in zip(A,b)]
 for j in range(n):
  k=next((i for i in range(j,n) if M[i][j]),None)
  if k is None:return None
  M[j],M[k]=M[k],M[j];v=M[j][j];M[j]=[a/v for a in M[j]]
  for i in range(n):
   if i!=j:
    v=M[i][j]
    if v:M[i]=[a-v*b for a,b in zip(M[i],M[j])]
 return [M[i][-1] for i in range(n)]
def exact_exists(equations,sources,point,inequalities):
 # Introduce a common positive slack for EVERY strict inequality. The source
 # cube and 0<=slack<=1 make a compact polytope. A positive maximum is achieved
 # at a vertex, even in lower-dimensional affine faces.
 rows=list(inequalities)+[(x,True) for x in sources]+[(1-x,True) for x in sources]
 rows +=[(e,False) for e in equations]+[(-e,False) for e in equations]
 constraints=[]
 for expr,strict in rows:
  expr=s.expand(expr.subs(point));a=[frac(expr.coeff(x)) for x in sources]+[F(-1 if strict else 0)]
  c=frac(expr.subs(dict.fromkeys(sources,0)));constraints.append((a,c))
 n=len(sources)+1
 constraints +=[([F(0)]*(n-1)+[F(1)],F(0)),([F(0)]*(n-1)+[F(-1)],F(1))]
 for ix in combinations(range(len(constraints)),n):
  v=solve([constraints[i][0] for i in ix],[-constraints[i][1] for i in ix])
  if v is not None and v[-1]>0 and all(sum(a*b for a,b in zip(coeff,v))+c>=0 for coeff,c in constraints):return True
 return False

def projected_contains(result,point):
 for cell in result['cells']:
  if any(int(s.sign(f.subs(point)))!=v for f,v in cell['signs'].items()):continue
  if all(bool(e.subs(point)>0 if st else e.subs(point)>=0) for e,st in cell['inequalities']):return True
 return False

x,y,a,b=s.symbols('x y a b');points=[dict(zip((a,b),v)) for v in product([s.Rational(-1),s.Rational(0),s.Rational(1,3),s.Rational(1,2),s.Rational(1)],repeat=2)]
cases=[('rank_zero_free_source',[a*x-b],[x,y],[]),('affine_equation_and_weak',[a*x+b*y-(a-b)],[x,y],[(x-y,False)]),('two_weak',[],[x,y],[(a*x-b,False),(b*x+a*y-s.Rational(1,3),False)]),('mixed_strict',[],[x,y],[(a*x-b,True),(b*x+a*y-s.Rational(1,3),False)]),('both_strict',[],[x,y],[(a*x-b,True),(b*x+a*y-s.Rational(1,3),True)]),('weak_equal_endpoint',[],[x,y],[(x-a,False),(a-x,False),(y-b,False),(b-y,False)]),('incompatible_strict_endpoint',[],[x,y],[(x-a,True),(a-x,False)]),('history_cell',[],[x,y],[(a-b,True),(a*x+b*y-s.Rational(1,3),False)])]
records=[]
for name,eq,src,ineq in cases:
 out=project_open_cube(eq,src,[a,b],ineq,max_branches=1000,max_pairs=10000)
 for point in points:
  u=exact_exists(eq,src,point,ineq);v=projected_contains(out,point);assert u==v,(name,point,u,v)
 records.append({'case':name,'exact_points':len(points),'sign_cells':len(out['cells'])})
r={'status':'PASS','method':'Independent Fraction vertex/slack existence oracle versus sign-cell compiler. No Z3 or second Fourier-Motzkin oracle used. Finite transcription controls only; uniform equivalence also hand-reviewed.','checks':records,'total':sum(x['exact_points'] for x in records),'source_sha256':hashlib.sha256((ROOT/'disposable/fourier_motzkin.py').read_bytes()).hexdigest()}
(ROOT/'INDEPENDENT-FRACTION-CONTROLS.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
