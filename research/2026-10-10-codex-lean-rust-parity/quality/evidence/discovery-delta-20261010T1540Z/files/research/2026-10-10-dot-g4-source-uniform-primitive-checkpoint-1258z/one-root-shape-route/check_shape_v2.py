from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from collections import defaultdict
import json

def forest(ts): return tuple(sorted(ts,key=repr))
def node(a,b): return tuple(sorted((a,b),key=repr))
def lam(k): return k*(k-1)//2

def merges(s):
 for i,j in combinations(range(len(s)),2):
  yield forest([s[k] for k in range(len(s)) if k not in (i,j)]+[node(s[i],s[j])])

@lru_cache(None)
def ordinary(s,q):
 if len(s)<2:return {s:F(1)}
 n=len(s); pol={s:{lam(n):F(1)}}; levels={n:{s}}
 for k in range(n-1,0,-1):
  incoming=defaultdict(lambda:defaultdict(F))
  for u in levels[k+1]:
   for v in merges(u):
    for e,c in pol[u].items():incoming[v][e]+=c
  levels[k]=set(incoming)
  for v,g in incoming.items():
   assert lam(k) not in g
   c={e:a/F(lam(k)-e) for e,a in g.items()}
   c[lam(k)]=-sum(c.values(),F(0))
   pol[v]=c
 out={v:sum((c*q**e for e,c in p.items()),F(0)) for v,p in pol.items()}
 assert sum(out.values())==1
 if 0<=q<=1: assert min(out.values())>=0
 return out

@lru_cache(None)
def cell(s,q,g):
 out=defaultdict(F);n=len(s)
 for bits in product((0,1),repeat=n):
  k=sum(bits);weight=g**k*(1-g)**(n-k)
  a=forest([s[i] for i in range(n) if bits[i]])
  b=forest([s[i] for i in range(n) if not bits[i]])
  for u,pu in ordinary(a,q).items():
   for v,pv in ordinary(b,q).items():out[forest(u+v)]+=weight*pu*pv
 assert sum(out.values())==1 and min(out.values())>=0
 return {k:v for k,v in out.items() if v}

def act(dist,kernel,*args):
 out=defaultdict(F)
 for s,p in dist.items():
  for t,q in kernel(s,*args).items():out[t]+=p*q
 return {s:p for s,p in out.items() if p}

def leaves(t):return 1 if isinstance(t,int) else leaves(t[0])+leaves(t[1])
def contrast(dist):
 one=sum((p for s,p in dist.items() if len(s)==1),F(0))
 bal=sum((p for s,p in dist.items() if len(s)==1 and not isinstance(s[0],int) and leaves(s[0][0])==2 and leaves(s[0][1])==2),F(0))
 return bal-one/3,one,bal

def summary(d):
 a,o,b=contrast(d);return {'contrast':str(a),'one_root':str(o),'balanced':str(b),'normalization':str(sum(d.values())),'state_count':len(d),'min_entry':str(min(d.values()))}

start={forest(range(4)):F(1)};results={}
for label,g,expected in [('fair',F(1,2),F(1,2400)),('biased',F(1,10),-F(237,500000))]:
 u=act(start,ordinary,F(1,2));u=act(u,cell,F(1,5),g)
 assert contrast(u)[0]==0
 uv=act(u,ordinary,F(1,2));uv=act(uv,cell,F(1,2),F(1,2))
 assert contrast(uv)[0]==expected
 p=g*(1-g);c4=p*(1-F(1,5))**2*(F(1,5)+2-2*p*(F(1,5)+5))/5
 assert expected==-F(10,3)*F(1,64)*c4*F(5,8)
 full=act(uv,ordinary,F(1,2));cancelled=act(full,ordinary,F(2))
 assert cancelled==uv
 results[label]={'g1':str(g),'p1':str(p),'c4_first_cell':str(c4),'before_postpad':summary(uv),'observed_endpoint':summary(full),'known_postpad_linear_cancellation_exact':True}
# One strict biased target with the identical COMMON clock.
t=act(start,ordinary,F(1,2));t=act(t,cell,F(1,20),F(1,3))
assert contrast(t)[0]==0
tfull=act(t,ordinary,F(1,2));assert act(tfull,ordinary,F(2))==t
results['target']={'g':str(F(1,3)),'cell_survival':str(F(1,20)),'before_postpad':summary(t),'observed_endpoint':summary(tfull)}
# Actual source controls: ordinary semigroup, arm exchange, no cell time.
assert act(act(start,ordinary,F(1,2)),ordinary,F(1,3))==act(start,ordinary,F(1,6))
assert cell(forest(range(4)),F(1,5),F(1,10))==cell(forest(range(4)),F(1,5),F(9,10))
assert cell(forest(range(4)),F(1),F(1,10))==start
results['controls']={'cap':4,'common_survival_all_three':str(F(1,80)),'ordinary_semigroup':True,'arm_exchange':True,'zero_cell_time':True,'all_physical_kernels_nonnegative_normalized':True}
results['scope']='Exact actual-source sign countercontrol only. Words are not asserted to match the target endpoint. The inverse ordinary matrix is used only as a known finite linear observable; it is not a permitted negative-time source.'
print(json.dumps(results,indent=2))
