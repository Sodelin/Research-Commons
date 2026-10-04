"""Independent bounded controls; no imported author code and no proof by testing."""
import json, hashlib
from pathlib import Path
HERE=Path(__file__).parent

def val2(n):
    assert n>0
    return (n & -n).bit_length()-1

def potential(n):
    return sum((len(r)+1)//2 for r in bin(n^(n>>1))[2:].split('0'))

def endpoints(n):
    out=set()
    for j in range(n.bit_length()):
        q,t=divmod(n,1<<j)
        out.add(n-2*t-1)
        h=q//2
        if h and val2(h)%2: out.add(n-(1<<j)-2*t-1)
    return out

class PathCheck:
    def __init__(self,a,b):
        word='10'*a+'010'*b+'0'
        self.width=len(word); self.n=int(word,2); self.initial=self.n
        self.g=[int(c) for c in f'{self.n^(self.n>>1):0{self.width}b}']
        self.edges=0; self.marked=False; self.slacks=[]
    def edge(self,new):
        old=self.n
        assert 0<=new<old and new in endpoints(old),(old,new)
        self.marked |= new==old-1 and val2(old)%2==1
        slack=1-potential(old)+potential(new)
        assert slack>=0
        self.slacks.append(slack); self.edges+=1; self.n=new
        self.g=[int(c) for c in f'{new^(new>>1):0{self.width}b}']
    def toggle(self,*ps):
        bits=self.g.copy()
        for p in ps: bits[p]^=1
        binary=[]; parity=0
        for x in bits: parity^=x; binary.append(str(parity))
        self.edge(int(''.join(binary),2))
    def A(self,s):
        assert sum(self.g[:s+1])%2==1
        self.toggle(s)
    def B(self,s,t):
        assert (t-s)>=2 and (t-s)%2==0 and t+1<self.width
        assert sum(self.g[:s+1])%2==1 and self.g[s+1]==1
        assert not any(self.g[s+2:t])
        self.toggle(s,t,t+1)
    def D(self,s,t):
        assert self.g[s:s+2]==[1,1] and self.g[t:t+2]==[1,1]
        assert not any(self.g[s+2:t])
        self.B(s,t); self.A(s+1)
    def R(self,s):
        assert self.g[s:s+6]==[1]*6
        self.B(s+2,s+4); self.B(s,s+2)
    def E(self,s,t,last_tail=True):
        assert self.g[s:s+4]==[1]*4
        self.B(s+2,t); self.B(s,s+2)
        if last_tail:self.D(s+1,t+3)
    def dominos(self):
        p=[]; i=0
        while i<self.width:
            if self.g[i]:
                assert self.g[i:i+2]==[1,1]
                p.append(i); i+=2
            else:i+=1
        return p
    def pair_delete(self,count):
        for _ in range(count//2):
            p=self.dominos(); self.D(p[0],p[1])
    def power_finish(self):
        assert self.n>1 and self.n&(self.n-1)==0
        assert val2(self.n)%2==1
        self.edge(self.n-1); self.edge(0)

def common_initial(p,a,b):
    ds=p.dominos(); s=ds[a-3]
    p.R(s); p.D(s+1,ds[a]); return a-3,b-1

def consume_E(p,A,B):
    while B>=2:
        ds=p.dominos(); p.E(ds[A-2],ds[A]); A-=2; B-=2
    return A,B

def even_reduce(p,a,b):
    assert a>b and (a-b)%2==0
    if not b:p.pair_delete(a); return
    A,B=common_initial(p,a,b); A,B=consume_E(p,A,B)
    if B:
        ds=p.dominos(); p.D(ds[A-1],ds[A]); A-=1
    p.pair_delete(A)

def plain(a,b):
    p=PathCheck(a,b)
    if (a-b)%2==0:even_reduce(p,a,b); expected=a+b
    else:
        p.edge(p.n-1); p.A(max(i for i,x in enumerate(p.g) if x))
        if b:even_reduce(p,a,b-1)
        else:p.pair_delete(a-1)
        expected=a+b+1
    assert p.n==0 and p.edges==expected
    return p

def marked(a,b):
    p=PathCheck(a,b)
    assert (a-b)%2==1 and a-b>=3
    if b==0:
        p.pair_delete(a-3); p.R(p.dominos()[0]); p.power_finish()
    else:
        A,B=common_initial(p,a,b); A,B=consume_E(p,A,B)
        if B==0:
            assert A%2==1 and val2(p.n)%2==1
            p.edge(p.n-1); p.A(max(i for i,x in enumerate(p.g) if x))
            p.pair_delete(A-1)
        else:
            assert A>=2 and A%2==0
            p.pair_delete(A-2); ds=p.dominos(); p.E(ds[0],ds[2],False); p.power_finish()
    assert p.n==0 and p.edges==a+b+1 and p.marked
    return p

counts={'plain_paths':0,'marked_paths':0,'actual_endpoint_edges':0,'max_binary_width':0}
for a in range(1,25):
    for b in range(a):
        paths=[plain(a,b)]; counts['plain_paths']+=1
        if (a-b)%2==1 and a-b>=3:
            paths.append(marked(a,b)); counts['marked_paths']+=1
        for p in paths:
            counts['actual_endpoint_edges']+=p.edges
            counts['max_binary_width']=max(counts['max_binary_width'],p.width)
            assert sum(p.slacks)==p.edges-(a+b)
proof=HERE.parent/'SEPARATION-FAMILY-CONSTRUCTIONS.md'
result={'status':'PASS','proof_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),'range':'1<=a<=24, 0<=b<a','counts':counts,'method':'Explicit constructions independently transcribed; every edge checked against full guarded numeric endpoint set, exact cost/slack/marker verified. These finite checks are not uniform proof premises.','imports_author_code':False}
(HERE/'FAMILY-CONSTRUCTION-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
