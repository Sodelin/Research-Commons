"""Independent, bounded exact audit of one retirement-time reset.

Reads the pinned public numeric JSON only. No external implementation imported.
"""
from pathlib import Path
from fractions import Fraction
from collections import Counter
import base64,gzip,hashlib,json,copy

SRC=Path('/workspace/shared/hamming-retired-frame-screen-20261011-1150z/bit-r767.json.gz.b64')
data=base64.b64decode(SRC.read_text())
assert hashlib.sha256(data).hexdigest()=='bd3b84244528767b85d8d7fe423b155630b5c659e21e51563674b1dcb6305ad7'
assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()=='807cea53ebe1322721463ee2319bcd52b9714f24'
src=json.loads(gzip.decompress(data))
assert (src['v'],src['R'],src['h'])==(120,767,8)
spaces=[set(s) for s in src['frames']]
def rational_rank(rows):
    basis={}
    for row in rows:
        w=list(map(Fraction,row))
        for j,b in sorted(basis.items()):
            q=w[j]
            if q:w=[x-q*y for x,y in zip(w,b)]
        pivot=next((j for j,x in enumerate(w) if x),None)
        if pivot is not None:
            q=w[pivot];basis[pivot]=[x/q for x in w]
    return len(basis)
rank=[rational_rank([src['lines'][j] for j in s]) for s in src['frames']]
old,new,cut,frame,drivers=252,949,1035,458,[0,1,512,523]
body=src['A']+src['B']
assert all(old not in [d]+ss for f,d,ss in body[cut+1:])
assert next(i for i,(f,d,ss) in enumerate(body) if new in [d]+ss)==1403
assert body[1403][0]==571 and spaces[frame]<=spaces[571]
assert rank[frame]==4 and rank[571]==5
assert old not in src['ret'] and new not in src['ret']
state=[1<<j if j<120 else 0 for j in range(1007)]
position=src['start'][:]
for f,d,ss in body[:cut+1]:
    for j in [d]+ss:position[j]=f
    for j in ss:state[d]^=state[j]
assert all(position[j]==frame for j in [old]+drivers)
assert state[old]==state[0]^state[1]^state[512]^state[523]
assert all(d>=120 and (d<240 or all(s<120 or s>=240 for s in ss)) for f,d,ss in body)

def build(omit_driver=None):
    q=copy.deepcopy(src)
    def ix(j):return old if j==new else j-int(j>new)
    q['R']=766
    for key in ('start','final'):q[key]=src[key][:new]+src[key][new+1:]
    q['ret']=[ix(j) for j in src['ret']]
    for phase in ('A','B'):
        word=[]
        for i,(f,d,ss) in enumerate(src[phase]):
            word.append([f,ix(d),[ix(s) for s in ss]])
            if phase=='A' and i==cut:
                word.append([frame,ix(old),[ix(s) for s in drivers if s!=omit_driver]])
        q[phase]=word
    # Compute the literal new helper-to-target response at zero sources/targets.
    z=[0]*240+[1<<j for j in range(q['R'])]
    for f,d,ss in q['A']:
        for s in ss:z[d]^=z[s]
    centers=[z[j] for j in q['ret']]
    for t,cs in enumerate(q['scatter']):
        for k in cs:z[120+t]^=centers[k]
    for f,d,ss in q['B']:
        for s in ss:z[d]^=z[s]
    q['D']=[[0,120+t,[240+j for j in range(q['R']) if z[120+t]>>j&1]] for t in range(120) if z[120+t]]
    q['C']=[[1,d,ss[:]] for f,d,ss in reversed(q['A']+q['B']) if d>=240]
    return q

def audit(q):
    n=240+q['R'];z=[1<<j for j in range(n)];pos=q['start'][:];hist=Counter()
    def touch(j,f):
        assert spaces[pos[j]]<=spaces[f],('non-nested',j,pos[j],f)
        step=rank[f]-rank[pos[j]]
        if step:hist[step]+=1
        pos[j]=f
    for phase in ('D','A','B','C'):
        if phase=='B':
            assert all(pos[j]==1 for j in q['ret']) and all(pos[j]==0 for j in range(120,240))
            cs=[z[j] for j in q['ret']];hist[8]+=len(cs)
            for t,ss in enumerate(q['scatter']):
                for k in ss:z[120+t]^=cs[k]
        for f,d,ss in q[phase]:
            assert d not in ss
            for j in [d]+ss:touch(j,f)
            for j in ss:z[d]^=z[j]
    for j,f in enumerate(q['final']):touch(j,f)
    expected=[1<<j for j in range(n)]
    for t in range(120):expected[120+t]^=1<<t
    assert z==expected,'all independent endpoint columns'
    return hist

before=audit(src);q=build();after=audit(q)
delta={r:after[r]-before[r] for r in sorted(before|after) if after[r]!=before[r]}
assert delta=={1:1,4:-1,5:-1}
assert sum(r*n for r,n in after.items())==8*766+240*7+9*8
for bad in drivers:
    try:audit(build(omit_driver=bad))
    except AssertionError:pass
    else:raise AssertionError(('missing reset driver accepted',bad))
assert all(not set(q['ret']).intersection(ss) for f,d,ss in q['A']+q['B'])
assert all(d not in q['ret'] for f,d,ss in q['B'])
for r in q['ret']:
    assert all(f==1 and all(s<120 for s in ss) for f,d,ss in q['A'] if d==r)
out={'status':'PASS_SCOPED_LOCAL_COLUMNS_AND_ROOT_CLOSED_NESTING','input_compressed_sha256':hashlib.sha256(data).hexdigest(),'reset':{'old':old,'new':new,'after_A_index':cut,'frame':frame,'drivers':drivers},'first_new_A_index':1403,'first_new_frame':571,'ranks':[4,5],'R':766,'columns':1006,'before':dict(sorted(before.items())),'after':dict(sorted(after.items())),'delta':delta,'negative_controls':'Each of four omitted reset drivers is rejected even after recomputing dirty correction.','limits':'No exported physical records, reflected global replay, Gram/projector recheck, phase/invoice or exponent certificate.'}
print(json.dumps(out,indent=2))

# Authenticate and independently compare the author's separately composed word.
composed_path=SRC.parent/'selected-retirement-word.json'
raw=composed_path.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='163f28b5e39c410d5c43c3f7af5409ec94eaff84ad73535122d77125c76be88e'
composed=json.loads(raw);deleted=set(q['ret']);keep=[j for j in range(1006) if j not in deleted]
number={j:i for i,j in enumerate(keep)}
def strip(word):return [[f,number[d],[number[s] for s in ss if s not in deleted]] for f,d,ss in word if d not in deleted]
baseA,baseB=strip(q['A']),strip(q['B'])
assert composed['A'][:len(baseA)]==baseA
T=composed['A'][len(baseA):]
assert len(T)==559 and composed['B']==list(reversed(T))+baseB
assert composed['D']==strip(q['D']) and composed['C']==strip(q['C'])
assert composed['start']==[q['start'][j] for j in keep] and composed['final']==[q['final'][j] for j in keep]
assert all(f==1 and d<120 and all(s<120 for s in ss) for f,d,ss in T)
forms=[1<<j for j in range(120)]
for f,d,ss in T:
    for s in ss:forms[d]^=forms[s]
for dest,ret in zip(composed['ret'],q['ret']):
    row=0
    for f,d,ss in q['A']:
        if d==ret:
            for s in ss:row^=1<<s
    assert forms[dest]==row
combined=audit(composed)
assert combined==Counter({1:2368,2:875,3:475,4:320,5:163,7:14,8:9})
assert composed['R']==757

def literal_events(w):
    result=[]
    for phase in ('D','A','B','C'):
        if phase=='B':
            for k,source in enumerate(w['ret']):
                result.append(('COPY',source,997))
                for t,ss in enumerate(w['scatter']):
                    if k in ss:result.append(('ADD',120+t,997))
                result.append(('ERASE',source,997))
        for f,d,ss in w[phase]:
            for s in ss:result.append(('ADD',d,s))
    return result

events=literal_events(composed)
def lifetime_and_bound(reverse):
    vectors=[1<<j for j in range(997)]+[0];weights=[1]*997+[0];maximum=1;live=None;adds=0;copies=0
    for op,d,s in (reversed(events) if reverse else events):
        if reverse and op!='ADD':op='COPY' if op=='ERASE' else 'ERASE'
        if op=='ADD':
            assert d!=live,'original source mutated within private episode'
            vectors[d]^=vectors[s];weights[d]+=weights[s];maximum=max(maximum,weights[d]);adds+=1
        elif op=='COPY':
            assert live is None and vectors[s]==0;live=d;vectors[s]=vectors[d];weights[s]=weights[d];copies+=1
        else:
            assert live==d and vectors[s]==vectors[d];live=None;vectors[s]=0;weights[s]=0
    expected=[1<<j for j in range(997)]+[0]
    for t in range(120):expected[120+t]^=1<<t
    assert live is None and vectors==expected
    return maximum,adds,copies
fw=lifetime_and_bound(False);rv=lifetime_and_bound(True)
assert fw==(4749591,14514,9) and rv==(18975330,14514,9)
assert ((1<<18)*fw[0]**5*rv[0]**4).bit_length()==226
print(json.dumps({'composed_sha256':hashlib.sha256(raw).hexdigest(),'status':'PASS_COMPOSED_SEMANTIC_MAP_997_COLUMNS_AND_SCALAR_LIFETIMES','source_basis_gates':len(T),'local_profile':dict(sorted(combined.items())),'forward_bound_adds_copies':fw,'reverse_bound_adds_copies':rv,'global_prefix_bits':226,'limits':'Reverse scalar/private-copy check only; no exported reflected physical-address or global bank replay.'},indent=2))
