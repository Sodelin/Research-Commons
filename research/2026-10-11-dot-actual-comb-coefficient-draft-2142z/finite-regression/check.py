"""Own bounded arithmetic check; no source-law or Lean acceptance claimed."""
import itertools, math, json, hashlib
from fractions import Fraction
from pathlib import Path

def graft(a,b):
    return tuple(sorted((a,b),key=repr))
def bad(t):
    if isinstance(t,int): return False
    def leaves(u):
        return {u} if isinstance(u,int) else leaves(u[0])|leaves(u[1])
    return 0 not in leaves(t) or bad(t[0]) or bad(t[1])

def run(k):
    target=0
    for a in range(1,k+1):target=graft(target,a)
    total=hits=union=0
    def visit(forest):
        nonlocal total,hits,union
        if len(forest)==1:
            total+=1; hits+=forest[0]==target; union+=not bad(forest[0]);return
        for i,j in itertools.combinations(range(len(forest)),2):
            visit(tuple(x for n,x in enumerate(forest) if n!=i and n!=j)+(graft(forest[i],forest[j]),))
    visit(tuple(range(k+1)))
    expected=Fraction(2**k,math.factorial(k+1)*math.factorial(k))
    assert Fraction(hits,total)==expected
    assert union==math.factorial(k)*hits
    return dict(k=k,unordered_histories=total,specified_comb_histories=hits,
        no_B_free_clade_histories=union,specified_mass=str(Fraction(hits,total)),
        union_mass=str(Fraction(union,total)),formula=str(expected))
if __name__=='__main__':
    print(json.dumps({'status':'FINITE_PYTHON_CHECK_ONLY','rows':[run(k) for k in range(1,7)],
      'scope':'Exhaustive unordered pair-merger histories on 2 through 7 distinct labels; not a proof of the actual Code law or arbitrary k.'},indent=2))
