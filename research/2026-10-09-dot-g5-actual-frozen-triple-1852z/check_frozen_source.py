"""Exact bounded check of the inherited ordered current-root merger primitive.
Not a Lean compilation, original-network sampler, or proof of the master G5.
"""
from collections import deque
import json, pathlib
import sympy as S
q=S.Symbol('q')
def initial(pop): return (tuple(range(3)),tuple(range(3)),tuple(('L',i) for i in range(3)),tuple(pop))
def successors(s):
 live,anc,trees,pop=s
 for a in live:
  for b in live:
   if a==b or pop[a]!=pop[b]: continue
   ll=tuple(x for x in live if x!=b)
   aa=tuple(a if x==b else x for x in anc)
   tt=list(trees);tt[a]=('G',trees[a],trees[b]);tt[b]=None
   pp=list(pop);pp[b]=None
   yield (ll,aa,tuple(tt),tuple(pp)),S.Rational(1,2)
def part(s):
 a=s[1]
 if a[0]==a[1]: return 4 if a[0]==a[2] else 1
 if a[0]==a[2]: return 2
 if a[1]==a[2]: return 3
 return 0
def check(pop,occ):
 states=[initial(pop)]; ix={states[0]:0}
 for s in states:
  for d,_ in successors(s):
   if d not in ix: ix[d]=len(states);states.append(d)
 n=len(states);Q=S.zeros(n)
 for i,s in enumerate(states):
  for d,r in successors(s):
   assert len(d[0])+1==len(s[0]); Q[i,ix[d]]+=r;Q[i,i]-=r
 assert Q*S.ones(n,1)==S.zeros(n,1)
 eig=sorted(set(Q[i,i] for i in range(n)));Exp=S.zeros(n)
 for lam in eig:
  P=S.eye(n)
  for nu in eig:
   if lam!=nu:P=P*(Q-nu*S.eye(n))/(lam-nu)
  Exp+=q**(-lam)*P
 assert S.simplify(Exp.subs(q,1)-S.eye(n))==S.zeros(n)
 # d/dt q=-q, matching rho=1 after common rescaling.
 assert S.simplify(-q*Exp.diff(q)-Exp*Q)==S.zeros(n)
 masses=[S.expand(sum(Exp[0,j] for j,s in enumerate(states) if part(s)==k)) for k in range(5)]
 if occ==0: expected=[1,0,0,0,0]
 elif occ==4: expected=[q**3,(q-q**3)/2,(q-q**3)/2,(q-q**3)/2,1-3*q/2+q**3/2]
 else:
  expected=[q,0,0,0,0];expected[occ]=1-q
 assert all(S.simplify(a-b)==0 for a,b in zip(masses,expected))
 pair=[]
 for a,b in [(0,1),(0,2),(1,2)]:
  v=S.expand(sum(Exp[0,j] for j,s in enumerate(states) if s[1][a]!=s[1][b]))
  assert v==(q if pop[a]==pop[b] else 1);pair.append(str(v))
 assert S.expand(sum(Exp[0,j] for j,s in enumerate(states) if len(s[0])==3))==Exp[0,0]
 return {'occupancy':occ,'states':n,'current_ordered_moves':sum(1 for s in states for _ in successors(s)), 'partition_masses':list(map(str,masses)), 'pair_survival':pair,'generator_and_ode':'PASS'}
results=[check(p,k) for k,p in enumerate([(0,1,2),(0,0,1),(0,1,0),(0,1,1),(0,0,0)])]
print(json.dumps({'status':'PASS','method':'exact rational symbolic finite current-root catalogue','scope':'five local occupancy patterns; normalized population pair rate 1; no calendar or Lean execution','cases':results},indent=2))
