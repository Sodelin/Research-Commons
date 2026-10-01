"""Exact confluent residual rank controls; not an all-factor classifier."""
from fractions import Fraction as F
from pathlib import Path
import hashlib,json,platform
import sympy as s

def R(q,k):return sum((q**a for a in range(k)),F(0))
def Rp(q,k):return sum((a*q**(a-1) for a in range(1,k)),F(0))

def main():
  cases=[]
  for M in range(2,15):
    ex=[j*(j-1)//2 for j in range(2,M+1)];d=M-1
    for alpha,beta in [(0,0),(1,0),(0,1),(1,1)]:
      for nodes in range(d//2+2):
        cols=[]
        if alpha:cols.append(s.Matrix(ex))
        if beta:cols.append(s.ones(d,1))
        for i in range(1,nodes+1):
          q=F(i,nodes+1)
          cols.extend([s.Matrix([s.Rational(R(q,k)) for k in ex]),
                       s.Matrix([s.Rational(Rp(q,k)) for k in ex])])
        J=s.Matrix.hstack(*cols) if cols else s.zeros(d,0)
        rank=J.rank()
        count=2*nodes+alpha+beta
        assert rank==min(d,count)
        cases.append({'cap':M,'positive_interior_nodes':nodes,
           'active_drift':alpha,'active_killing':beta,'rank':rank,
           'claimed_sufficient_threshold_met':count>=d})
  out={'status':'PASS','python':platform.python_version(),'sympy':s.__version__,
    'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'exact_confluent_rank_controls':len(cases),
    'sufficient_attainment_controls':sum(x['claimed_sufficient_threshold_met'] for x in cases),
    'cases':cases,
    'limits':'Finite exact rational rank controls only. The all-cap root-count and normal-form theorem are hand proofs; no exact total factor bound, arbitrary closure-membership test, or cap-eight decision.'}
  Path(__file__).with_name('singular-rank-checks.json').write_text(json.dumps(out,indent=2)+'\n')
  print(json.dumps({k:v for k,v in out.items() if k!='cases'},indent=2))
if __name__=='__main__':main()
