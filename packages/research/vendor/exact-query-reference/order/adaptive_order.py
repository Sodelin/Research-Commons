"""Deterministic adaptive common-order learner for circular binary-tree families.

Author: ASTRA-EXACT-QUERY-20260930T1156Z. Research implementation, standard
library only. Correctness is the separate written invariant, not finite tests.
An oracle returns a complete 1/2/4 bit mask on SORTED distinct quartet labels.
The learner receives labels and that oracle, never the displayed trees/splits.
"""
from itertools import product
from collections import Counter
from core import pair_bit, filter_gaps
from insertion import learn_all_gaps


def canonical_circle(order):
    order=tuple(order); k=order.index(min(order)); f=order[k:]+order[:k]
    return min(f,(f[0],)+tuple(reversed(f[1:])))


class CircularTree:
    """Unrooted tree; each internal rotation may independently be reversed."""
    def __init__(self, taxa):
        taxa=tuple(taxa)
        if len(taxa)!=3 or len(set(taxa))!=3 or min(taxa)<0:
            raise ValueError('Initialize with three distinct nonnegative labels.')
        self.rot={-1:list(taxa)}
        self.rot.update({t:[-1] for t in taxa})
        self.taxa=set(taxa)

    def validate(self):
        assert all(len(set(ns))==len(ns) for ns in self.rot.values())
        assert all(u in self.rot[v] for u,ns in self.rot.items() for v in ns)
        assert sum(map(len,self.rot.values()))==2*(len(self.rot)-1)
        assert self.component(next(iter(self.rot)),None)==set(self.rot)
        assert all(len(ns)==1 if v in self.taxa else len(ns)>=3 for v,ns in self.rot.items())
        assert len(self.rot)-len(self.taxa)<=len(self.taxa)-2

    def component(self,start,blocked,allowed=None):
        if allowed is None:allowed=self.rot
        if start not in allowed or start==blocked:return set()
        out={start};todo=[start]
        while todo:
            u=todo.pop()
            for v in self.rot[u]:
                if v!=blocked and v in allowed and v not in out:
                    out.add(v);todo.append(v)
        return out

    def representatives(self,v):
        if v in self.taxa:raise ValueError('No local rotation at a leaf.')
        return tuple(min(self.component(u,v)&self.taxa) for u in self.rot[v])

    def one_order(self,flipped=frozenset()):
        r=min(self.taxa);out=[r];todo=[(self.rot[r][0],r)]
        while todo:
            v,parent=todo.pop()
            if v in self.taxa:
                out.append(v);continue
            ns=list(self.rot[v])
            if v in flipped:ns.reverse()
            i=ns.index(parent);children=ns[i+1:]+ns[:i]
            todo.extend((u,v) for u in reversed(children))
        return canonical_circle(out)

    def all_orders(self):
        internal=sorted(set(self.rot)-self.taxa)
        return {self.one_order(frozenset(v for v,b in zip(internal,bits) if b))
                for bits in product((False,True),repeat=len(internal))}

    def subdivide(self,u,v,z):
        t=min(self.rot)-1
        assert v in self.rot[u] and z not in self.rot
        self.rot[u][self.rot[u].index(v)]=t
        self.rot[v][self.rot[v].index(u)]=t
        self.rot[t]=[u,z,v];self.rot[z]=[t];self.taxa.add(z)
        self.validate()

    @staticmethod
    def add_marker(rotation,corner,z):
        a,b=corner; out=list(rotation)
        for i,u in enumerate(out):
            if {u,out[(i+1)%len(out)]}=={a,b}:
                return out[:i+1]+[z]+out[i+1:]
        raise AssertionError(('not a corner',rotation,corner))

    @staticmethod
    def without_edge(rotation,neighbor):
        i=rotation.index(neighbor)
        return rotation[i+1:]+rotation[:i]

    def merge_path(self,path,corners,z):
        """Glue rotations along the path, identifying adjacent z markers."""
        assert path and len(set(path))==len(path) and z not in self.rot
        seq=self.add_marker(self.rot[path[0]],corners[path[0]],z)
        for prev,w in zip(path,path[1:]):
            left=self.without_edge(seq,w)
            initial=self.add_marker(self.rot[w],corners[w],z)
            chosen=None
            for orient in (initial,list(reversed(initial))):
                right=self.without_edge(orient,prev)
                merged=left+right; positions=[i for i,x in enumerate(merged) if x==z]
                assert len(positions)==2
                i,j=positions
                if j-i==1 or (i==0 and j==len(merged)-1):
                    chosen=merged[:j]+merged[j+1:];break
            assert chosen is not None,('markers did not meet',path,corners,seq,initial)
            seq=chosen
        assert len(seq)==len(set(seq)) and not(set(seq)&set(path))
        t=min(self.rot)-1; pathset=set(path)
        for u in seq:
            if u==z:continue
            old=[v for v in self.rot[u] if v in pathset];assert len(old)==1
            self.rot[u][self.rot[u].index(old[0])]=t
        for v in path:del self.rot[v]
        self.rot[t]=seq;self.rot[z]=[t];self.taxa.add(z)
        self.validate()


class AdaptiveOrderLearner:
    def __init__(self,taxa,oracle):
        self.labels=tuple(taxa)
        if len(self.labels)<3 or len(set(self.labels))!=len(self.labels) or min(self.labels)<0:
            raise ValueError('Need >=3 distinct nonnegative integer labels.')
        self.oracle=oracle;self.cache={};self.stats=Counter();self.history=[]
        self.tree=CircularTree(self.labels[:3]);self.z=None;self._reps={}

    def query(self,q):
        q=tuple(sorted(q))
        if len(q)!=4 or len(set(q))!=4:raise ValueError('Illegal quartet.')
        if q not in self.cache:
            ans=self.oracle(q)
            if type(ans) is not int or ans not in (1,2,3,4,5,6):
                raise ValueError('Oracle violates nonempty circular binary support promise.')
            self.cache[q]=ans
        return self.cache[q]

    def reps(self,v):
        if v not in self._reps:self._reps[v]=self.tree.representatives(v)
        return self._reps[v]

    def arrow_test(self,v,u):
        """One query exactly recognizes the local arrow to u."""
        if v in self.tree.taxa:return True
        ns=self.tree.rot[v];i=ns.index(u);r=self.reps(v);d=len(r)
        q=tuple(sorted((self.z,r[(i-1)%d],r[i],r[(i+1)%d])))
        self.stats['arrow_predicates']+=1
        return self.query(q)==pair_bit(q,(self.z,r[i]))

    def local_corner(self,v):
        r=self.reps(v); ns=self.tree.rot[v]
        gaps=learn_all_gaps(r,self.z,self.query,promised=True)
        assert len(gaps)==1,('not central',v,gaps,r)
        i=next(iter(gaps));self.stats['central_corner_calls']+=1
        return (ns[i],ns[(i+1)%len(ns)])

    def biased_classify(self,v,weights):
        """Return an arrow neighbor, or None for central. Zero-weight arrow
        alternatives have already been excluded by the search-region invariant.
        """
        if v in self.tree.taxa:return self.tree.rot[v][0]
        ns=self.tree.rot[v];r=self.reps(v);d=len(ns)
        gaps=set(range(d)); active={i for i,u in enumerate(ns) if weights.get(u,0)>0}
        while active:
            W=sum(weights[ns[i]] for i in active)
            heavy=max(active,key=lambda i:(weights[ns[i]],-i))
            if 6*weights[ns[heavy]]>W:
                cuts=((heavy-1)%d,heavy,(heavy+1)%d)
            else:
                ordered=sorted(active); chunks=[];cur=[];s=0
                for i in ordered:
                    cur.append(i);s+=weights[ns[i]]
                    if len(chunks)<2 and 4*s>=W:
                        chunks.append(cur);cur=[];s=0
                chunks.append(cur)
                assert len(chunks)==3 and all(chunks)
                assert all(6*sum(weights[ns[i]] for i in c)>=W for c in chunks)
                cuts=tuple(c[0] for c in chunks)
            q=tuple(sorted((self.z,)+tuple(r[i] for i in cuts)))
            ans=self.query(q);self.stats['biased_predicates']+=1
            if 6*weights[ns[heavy]]>W and ans==pair_bit(q,(self.z,r[heavy])):
                return ns[heavy]
            gaps=filter_gaps(r,self.z,cuts,ans,gaps)
            active={i for i in active if i in gaps and (i-1)%d in gaps}
            after=sum(weights[ns[i]] for i in active)
            assert 6*after<=5*W,('weight reduction failed',W,after,cuts)
        return None

    def find_central(self):
        B=self.tree;U=set(B.rot)
        while U:
            self.stats['centroid_steps']+=1
            # Compute a centroid of the connected search region in linear
            # tree work, without materializing every vertex's component sets.
            root=min(U);parent={root:None};traversal=[root]
            for x in traversal:
                for y in B.rot[x]:
                    if y in U and y!=parent[x]:
                        assert y not in parent
                        parent[y]=x;traversal.append(y)
            assert set(traversal)==U
            sizes={x:1 for x in U}
            for x in reversed(traversal[1:]):sizes[parent[x]]+=sizes[x]
            best=None
            for x in U:
                w={y:(sizes[y] if parent.get(y)==x else len(U)-sizes[x] if y==parent[x] else 0) for y in B.rot[x]}
                score=max(w.values(),default=0)
                if best is None or (score,x)<best[:2]:best=(score,x,w)
            largest,v,weights=best
            assert 2*largest<=len(U)
            u=self.biased_classify(v,weights)
            if u is None:return ('vertex',v)
            if self.arrow_test(u,v):return ('edge',v,u)
            U=B.component(u,v,U)
        raise AssertionError('Search lost the central path.')

    def step(self,z):
        if z in self.tree.taxa:raise ValueError('Taxon already present.')
        self.z=z;self._reps={};before=len(self.cache);oldnodes=len(self.tree.rot)-len(self.tree.taxa)
        located=self.find_central()
        if located[0]=='edge':
            _,u,v=located;self.tree.subdivide(u,v,z);path=[];corners={}
        else:
            start=located[1];corners={start:self.local_corner(start)}
            def arm(prev,v):
                out=[]
                while not self.arrow_test(v,prev):
                    assert v not in corners,('central path loop',v,corners)
                    corners[v]=self.local_corner(v)
                    assert prev in corners[v],('incoming edge not in corner',prev,v,corners[v])
                    out.append(v)
                    nxt=next(x for x in corners[v] if x!=prev)
                    prev,v=v,nxt
                return out
            a,b=corners[start]
            left=arm(start,a);right=arm(start,b)
            path=list(reversed(left))+[start]+right
            self.tree.merge_path(path,corners,z)
        newnodes=len(self.tree.rot)-len(self.tree.taxa)
        assert newnodes-oldnodes==(1-len(path) if path else 1)
        self.history.append({'taxon':z,'new_queries':len(self.cache)-before,'central_nodes':len(path),
                             'internal_nodes_before':oldnodes,'internal_nodes_after':newnodes,
                             'local_corners':{str(v):list(c) for v,c in corners.items()}})
        return self.tree.one_order()

    def run(self,after_step=None):
        for z in self.labels[3:]:
            self.step(z)
            if after_step is not None:after_step(self)
        return self.tree.one_order()
