"""Exact finite deterministic minimax, with independently replayable JSON certificates."""
from functools import lru_cache
from itertools import combinations
from collections import defaultdict
import json,time,hashlib,sys

ANSWERS=(1,2,3,4,5,6)

def members(s):
    out=[]
    while s:
        b=s&-s;out.append(b.bit_length()-1);s^=b
    return out

class Solver:
    def __init__(self,rows):
        self.rows=tuple(tuple(r) for r in rows);self.N=len(rows);self.m=len(rows[0]);self.full=(1<<self.N)-1
        assert len(set(self.rows))==self.N
        bufs=[[bytearray((self.N+7)//8) for a in ANSWERS] for q in range(self.m)]
        for i,r in enumerate(rows):
            assert len(r)==self.m
            for q,a in enumerate(r):bufs[q][ANSWERS.index(a)][i//8]|=1<<(i%8)
        self.parts=[[int.from_bytes(b,'little') for b in bs] for bs in bufs]
        self.bounds={};self.calls=0
    def partitions(self,s):
        opts=[]
        for q in range(self.m):
            cs=[(a,s&p) for a,p in zip(ANSWERS,self.parts[q]) if s&p]
            if len(cs)<2:continue
            cs.sort(key=lambda x:x[1].bit_count(),reverse=True);sizes=[x.bit_count() for _,x in cs]
            opts.append((sizes[0],sum(x*x for x in sizes),q,cs))
        opts.sort(key=lambda x:x[:3]);return opts
    def can(self,s,d):
        self.calls+=1;c=s.bit_count()
        if c<=1:return True
        if d<=0 or c>6**d:return False
        lo,hi,best=self.bounds.get(s,(1,self.m,-1))
        if d<lo:return False
        if d>=hi:return True
        for largest,_,q,cs in self.partitions(s):
            if largest>6**(d-1):continue
            if all(self.can(t,d-1) for _,t in cs):
                self.bounds[s]=(lo,min(hi,d),q);return True
        self.bounds[s]=(max(lo,d+1),hi,best);return False
    def minimum(self):
        for d in range(self.m+1):
            if self.can(self.full,d):return d
        raise AssertionError('distinct full profiles not separable')
    def upper(self,k):
        nodes=[];memo={}
        def rec(s,d):
            key=(s,d)
            if key in memo:return memo[key]
            i=len(nodes);nodes.append(None);memo[key]=i
            if s.bit_count()==1:nodes[i]={'leaf':members(s)[0]};return i
            for _,_,q,cs in self.partitions(s):
                if all(self.can(t,d-1) for _,t in cs):
                    nodes[i]={'query':q,'branches':[[a,rec(t,d-1)] for a,t in sorted(cs)]};return i
            raise AssertionError('upper extraction failed')
        root=rec(self.full,k);return {'depth':k,'root':root,'nodes':nodes}
    def lower(self,d):
        assert not self.can(self.full,d)
        nodes=[];memo={}
        def rec(s,budget):
            key=(s,budget)
            if key in memo:return memo[key]
            i=len(nodes);memo[key]=i;nodes.append(None)
            node={'rows':members(s),'budget':budget}
            if s.bit_count()>6**budget:
                node['rule']='count';nodes[i]=node;return i
            node['rule']='adversary';choices=[]
            # Nonpartitioning queries can be deleted from an optimal strategy.
            for _,_,q,cs in self.partitions(s):
                for a,t in cs:
                    if not self.can(t,budget-1):
                        choices.append([q,a,rec(t,budget-1)]);break
                else:raise AssertionError('missing lower branch')
            assert choices
            node['choices']=sorted(choices);nodes[i]=node;return i
        root=rec(self.full,d);return {'budget':d,'root':root,'nodes':nodes}

def verify_upper(rows,cert):
    """Independent checker: no optimizer, bound cache, or partition bitsets."""
    N=len(rows);m=len(rows[0]);nodes=cert['nodes'];seen={};active=set();reached=set()
    def visit(i,ids,left):
        sig=(tuple(ids),left)
        if i in seen:assert seen[i]==sig;return
        assert i not in active and 0<=i<len(nodes);active.add(i);node=nodes[i]
        if 'leaf' in node:
            assert len(ids)==1 and node['leaf']==ids[0];reached.add(ids[0])
        else:
            assert left>0;q=node['query'];assert 0<=q<m
            groups=defaultdict(list)
            for j in ids:groups[rows[j][q]].append(j)
            branches=dict(node['branches']);assert len(branches)==len(node['branches']) and set(branches)==set(groups)
            assert len(groups)>=2
            for a,g in groups.items():visit(branches[a],g,left-1)
        active.remove(i);seen[i]=sig
    visit(cert['root'],list(range(N)),cert['depth'])
    assert reached==set(range(N));return {'nodes':len(seen),'terminal_profiles':len(reached)}

def verify_lower(rows,cert):
    """Replay every adversarial choice, including every informative query."""
    N=len(rows);m=len(rows[0]);nodes=cert['nodes'];done=set();active=set()
    def visit(i,required,budget):
        assert 0<=i<len(nodes);node=nodes[i];ids=node['rows']
        assert ids==required and node['budget']==budget
        assert len(set(ids))==len(ids) and all(0<=j<N for j in ids)
        if i in done:return
        assert i not in active;active.add(i)
        if node['rule']=='count':assert len(ids)>6**budget
        else:
            assert node['rule']=='adversary' and budget>0
            choices={q:(a,nxt) for q,a,nxt in node['choices']};assert len(choices)==len(node['choices'])
            informative=set()
            for q in range(m):
                groups=defaultdict(list)
                for j in ids:groups[rows[j][q]].append(j)
                if len(groups)<2:continue
                informative.add(q);assert q in choices
                a,nxt=choices[q];assert a in groups;visit(nxt,groups[a],budget-1)
            assert set(choices)==informative and informative
        active.remove(i);done.add(i)
    visit(cert['root'],list(range(N)),cert['budget']);return {'nodes':len(done)}

def canonical_bytes(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def sha(x):return hashlib.sha256(canonical_bytes(x)).hexdigest()

if __name__=='__main__':
    n=int(sys.argv[1]) if len(sys.argv)>1 else 6
    data=json.load(open(f'labeled-{n}.json'));rows=[tuple(r['profile']) for r in data['rows']]
    t=time.monotonic();s=Solver(rows);k=s.minimum();print('minimum',n,k,'states',len(s.bounds),'sec',time.monotonic()-t,flush=True)
    up=s.upper(k);low=s.lower(k-1)
    checks={'upper':verify_upper(rows,up),'lower':verify_lower(rows,low)}
    cert={'n':n,'catalogue_sha256':sha(data['rows']),'minimum':k,'upper':up,'lower':low}
    open(f'certificate-{n}.json','wb').write(canonical_bytes(cert))
    report={'n':n,'profile_count':len(rows),'minimum':k,'solver_states':len(s.bounds),'calls':s.calls,
            'checks':checks,'catalogue_sha256':sha(data['rows']),'certificate_sha256':sha(cert),'seconds':time.monotonic()-t}
    json.dump(report,open(f'result-{n}.json','w'),indent=2);print(json.dumps(report,indent=2),flush=True)
