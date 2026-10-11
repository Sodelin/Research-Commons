"""Own retirement reset plus inherited source-basis construction check.

The only executed import is our own exact checker. External input is JSON data.
This supplies local finite-word evidence, not complete recursive admission.
"""
import runpy,json,hashlib,math
from pathlib import Path
P=Path(__file__).parent
ns=runpy.run_path(str(P/'check_retirement_variants.py'))
c=ns['c'];audit=ns['audit'];dim=ns['dim'];change=ns['change']
p=next(p for p in json.loads((P/'retirement-reset-candidates.json').read_text())if p['old']==252)
q=change(p,949)
def centre_basis(w):
 v=w['v'];ret=set(w['ret']);n=2*v+w['R'];rows=[]
 for rr in w['ret']:
  z=0
  for f,d,ss in w['A']:
   if d==rr:
    assert f==1 and all(s<v for s in ss)
    for s in ss:z^=1<<s
  rows.append(z)
 assert all(not ret.intersection(ss) for f,d,ss in w['A']+w['B'])
 assert all(d not in ret for f,d,ss in w['B'])
 piv={}
 for z in rows:
  for k,a in sorted(piv.items()):
   if z>>k&1:z^=a
  assert z;k=(z&-z).bit_length()-1;piv[k]=z
 targets=sorted(piv);mat=[1<<i for i in range(v)]
 for d,z in zip(targets,rows):mat[d]=z
 gates=[]
 def rowadd(d,s):mat[d]^=mat[s];gates.append([1,d,[s]])
 for k in range(v):
  s=next(i for i in range(k,v)if mat[i]>>k&1)
  if s!=k:rowadd(k,s);rowadd(s,k);rowadd(k,s)
  for i in range(v):
   if i!=k and mat[i]>>k&1:rowadd(i,k)
 assert mat==[1<<i for i in range(v)]
 keep=[r for r in range(n)if r not in ret];ix={r:i for i,r in enumerate(keep)}
 def remap(gs):return[[f,ix[d],[ix[s]for s in ss if s not in ret]]for f,d,ss in gs if d not in ret]
 out={**w,'R':w['R']-len(ret),'ret':targets,'A':remap(w['A'])+list(reversed(gates)),'B':gates+remap(w['B']),'C':remap(w['C']),'D':remap(w['D']),'start':[w['start'][r]for r in keep],'final':[w['final'][r]for r in keep]}
 return out,len(gates),rows
base,bg,br=centre_basis(c);new,ng,nr=centre_basis(q);assert bg==ng==559 and br==nr
bh=audit(base);nh=audit(new)
print('COMPOSED all-column and nested PASS',new['R'],240+new['R'],dict(sorted(nh.items())))
assert new['R']==757
# Own literal scalar stream, including centre lifetime and signed inverse order.
def stream(w):
 n=240+w['R'];ev=[]
 for ph in ['D','A','B','C']:
  if ph=='B':
   for k,r in enumerate(w['ret']):
    ev.append(('copy',r,n))
    for t,ss in enumerate(w['scatter']):
     if k in ss:ev.append(('add',120+t,n))
    ev.append(('erase',r,n))
  for f,d,ss in w[ph]:
   for s in ss:ev.append(('add',d,s))
 return ev
def norm_replay(w,reverse):
 n=240+w['R'];z=[1<<i for i in range(n)]+[0];a=[1]*n+[0];bound=1;active=None;adds=0;copies=0
 es=stream(w)
 for op,d,s in (reversed(es)if reverse else es):
  if reverse:op={'copy':'erase','erase':'copy','add':'add'}[op]
  if op=='add':z[d]^=z[s];a[d]+=a[s];bound=max(bound,a[d]);adds+=1
  elif op=='copy':assert active is None and z[s]==0;active=d;z[s]=z[d];a[s]=a[d];copies+=1
  else:assert active==d and z[s]==z[d];z[s]=0;a[s]=0;active=None
 assert active is None
 want=[1<<i for i in range(n)]+[0]
 for t in range(120):want[120+t]^=1<<t
 assert z==want
 return dict(bound=bound,adds=adds,copies=copies)
bf=norm_replay(base,False);bb=norm_replay(base,True);nf=norm_replay(new,False);nb=norm_replay(new,True)
print('baseline norm',bf,bb);print('candidate norm',nf,nb)
prefix=(1<<18)*nf['bound']**5*nb['bound']**4
print('candidate global prefix bits',prefix.bit_length(),'charge',64*math.ceil(prefix.bit_length()/64))
# The fixed compressed-nine schedule has unchanged idle paths.
idle={7:5760,14:3840,28:3840,42:3840}
globalH={k:72*nh[k]+idle.get(k,0)for k in sorted(set(nh)|set(idle))}
W=7680+9*757;mass=sum(k*z for k,z in globalH.items());assert 64*W-mass==2496
record=dict(status='OWN_LOCAL_ALL_COLUMN_NESTED_AND_NORM_PASS',source_git_blob='807cea53ebe1322721463ee2319bcd52b9714f24',candidate={**p,'new':949},R=757,local_columns=997,source_basis_gates=ng,local_profile=dict(sorted(nh.items())),global_profile=globalH,live=W,physical=W+9,mass=mass,deficit=2496,forward=nf,reverse=nb,global_prefix_bits=prefix.bit_length(),charged_prefix_bits=64*math.ceil(prefix.bit_length()/64),remaining=['independent candidate review','full compiler records and coefficient invoice','both orientation physical address admission','two exact pricing engines and outer assembly'])
for name,data in [('selected-retirement-word.json',new),('selected-retirement-receipt.json',record)]:
 raw=(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n').encode();(P/name).write_bytes(raw);print(name,len(raw),hashlib.sha256(raw).hexdigest())
print('PASS selected composition')
