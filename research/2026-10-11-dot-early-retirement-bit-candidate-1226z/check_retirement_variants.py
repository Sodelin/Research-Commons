"""Own exact local bit-word checker and retirement-time reset transformation.

Only JSON is read. No upstream Python is imported or executed.
"""
import base64,gzip,json,copy,time,math
from collections import Counter
from pathlib import Path
P=Path(__file__).parent;c=json.loads(gzip.decompress(base64.b64decode((P/'bit-r767.json.gz.b64').read_text())))
masks=[sum(1<<s for s in a)for a in c['frames']]
def rank(rows):
 b={}
 for z in rows:
  z=z[:]
  for k,w in sorted(b.items()):
   if z[k]:
    a,d=z[k],w[k];z=[d*x-a*y for x,y in zip(z,w)]
    g=math.gcd(*z)
    if g:z=[x//g for x in z]
  k=next((j for j,x in enumerate(z)if x),None)
  if k is not None:b[k]=z
 return len(b)
dim=[rank([c['lines'][j]for j in f])for f in c['frames']]
def audit(q):
 v=q['v'];n=2*v+q['R'];value=[1<<r for r in range(n)];cur=q['start'][:];hist=Counter()
 def climb(r,f):
  assert not masks[cur[r]]&~masks[f],('frame',r,cur[r],f)
  d=dim[f]-dim[cur[r]]
  if d:hist[d]+=1
  cur[r]=f
 for phase in ['D','A','B','C']:
  if phase=='B':
   assert all(cur[r]==1 for r in q['ret']);assert all(cur[r]==0 for r in range(v,2*v))
   ts=[value[r]for r in q['ret']];hist[8]+=len(ts)
   for t,ss in enumerate(q['scatter']):
    for s in ss:value[v+t]^=ts[s]
  for f,d,ss in q[phase]:
   assert d not in ss
   for r in [d]+ss:climb(r,f)
   for s in ss:value[d]^=value[s]
 for r,f in enumerate(q['final']):climb(r,f)
 expected=[1<<r for r in range(n)]
 for t in range(v):expected[v+t]^=1<<t
 assert value==expected,'all-column endpoint'
 assert sum(k*z for k,z in hist.items())==8*q['R']+2*v*7+8*len(q['ret'])
 return hist
def change(p,new,omit=False):
 q=copy.deepcopy(c);old=p['old'];at=p['reset_after'];f=p['frame'];parents=p['reset_sources'];n=240+c['R']
 ops=c['A']+c['B'];assert all(old not in[d]+ss for ff,d,ss in ops[at+1:]);assert all(new not in[d]+ss for ff,d,ss in ops[:at+1]);assert old not in c['ret'] and new not in c['ret']
 vals=[1<<r if r<120 else 0 for r in range(n)]
 for ff,d,ss in ops[:at+1]:
  for s in ss:vals[d]^=vals[s]
 z=vals[old]
 for s in parents:z^=vals[s]
 assert z==0
 keep=[r for r in range(n)if r!=new];ix={r:i for i,r in enumerate(keep)}
 def name(r):return ix[old if r==new else r]
 q['R']-=1;q['ret']=[name(r)for r in c['ret']];q['start']=[c['start'][r]for r in keep];q['final']=[c['final'][r]for r in keep]
 for phase,offset in [('A',0),('B',len(c['A']))]:
  gs=[]
  for i,(ff,d,ss)in enumerate(c[phase]):
   gs.append([ff,name(d),[name(s)for s in ss]])
   if i+offset==at and not omit:gs.append([f,name(old),[name(s)for s in parents]])
  q[phase]=gs
 # Recompute exact dirty response and full-frame inverse helper subword.
 n-=1;v=[0]*240+[1<<(r-240)for r in range(240,n)]
 for ff,d,ss in q['A']:
  for s in ss:v[d]^=v[s]
 totals=[v[r]for r in q['ret']]
 for t,ss in enumerate(q['scatter']):
  for s in ss:v[120+t]^=totals[s]
 for ff,d,ss in q['B']:
  for s in ss:v[d]^=v[s]
 q['D']=[[0,120+t,[240+j for j in range(q['R'])if v[120+t]>>j&1]]for t in range(120)if v[120+t]]
 q['C']=[[1,d,ss[:]]for ff,d,ss in reversed(q['A']+q['B'])if d>=240]
 return q
t0=time.monotonic();old=audit(c);print('baseline all-column/nested PASS',dict(sorted(old.items())))
results=[]
for p in json.loads((P/'retirement-reset-candidates.json').read_text()):
 for new in p['new_options']:
  q=change(p,new);h=audit(q);delta={k:h[k]-old[k]for k in sorted(set(h)|set(old))if h[k]!=old[k]}
  results.append(dict(old=p['old'],new=new,reset_after=p['reset_after'],frame=p['frame'],reset_sources=p['reset_sources'],delta=delta))
print('legal all-column variants',len(results),'seconds',round(time.monotonic()-t0,3))
print(json.dumps(results[:15],indent=2))
(P/'retirement-variant-results.json').write_text(json.dumps(results,separators=(',',':'))+'\n')
