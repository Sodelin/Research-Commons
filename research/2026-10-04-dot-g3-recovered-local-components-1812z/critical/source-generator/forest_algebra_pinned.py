"""Exact finite-cap forest algebra for source-realizable coalescent testers.

All probability arithmetic is rational.  Forest labels are retained.  A common
hybrid uses one coin for the entire entering forest; independent inheritance
uses one choice per surviving lineage.  Symbolic polynomial coefficients are
used only to certify spans, never as biological source parameters.
"""
from __future__ import annotations
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations, product
from math import comb
from typing import Any, Iterable

Tree = Any  # int leaf, or canonical tuple[Tree, Tree]
Forest = tuple[Tree, ...]
Poly = dict[tuple[int, ...], Q]

def leaves(t: Tree) -> tuple[int, ...]:
    if isinstance(t, int):
        return (t,)
    return tuple(sorted(leaves(t[0]) + leaves(t[1])))

def tree(a: Tree, b: Tree) -> Tree:
    return (a,b) if min(leaves(a)) < min(leaves(b)) else (b,a)

def forest(ts: Iterable[Tree]) -> Forest:
    return tuple(sorted(ts, key=lambda t: min(leaves(t))))

def relabel(t: Tree, mapping: dict[int, Any]) -> Tree:
    if isinstance(t, int):
        return mapping[t]
    return tree(relabel(t[0], mapping), relabel(t[1], mapping))

def graft(f: Forest, g: Forest) -> Forest:
    """Substitute f's roots for the token leaves of g, preserving subtrees."""
    return forest(relabel(t, dict(enumerate(f))) for t in g)

@lru_cache(None)
def trees(labels: tuple[int,...]) -> tuple[Tree,...]:
    if len(labels) == 1:
        return (labels[0],)
    if not labels:
        return ()
    ans=[]
    rest=labels[1:]
    for k in range(len(rest)):
        for sub in combinations(rest,k):
            left=(labels[0],)+sub
            right=tuple(a for a in labels if a not in left)
            ans.extend(tree(a,b) for a in trees(left) for b in trees(right))
    return tuple(ans)

@lru_cache(None)
def forests(labels: tuple[int,...]) -> tuple[Forest,...]:
    if not labels:
        return ((),)
    ans=[]
    rest=labels[1:]
    for k in range(len(rest)+1):
        for sub in combinations(rest,k):
            block=(labels[0],)+sub
            other=tuple(a for a in labels if a not in block)
            ans.extend(forest((t,)+f) for t in trees(block) for f in forests(other))
    return tuple(sorted(ans, key=repr))

@lru_cache(None)
def embedded_merger_law(k:int,r:int) -> dict[Forest,Q]:
    if not 0 <= r <= k or (r == 0 and k):
        return {}
    law={tuple(range(k)):Q(1)}
    for j in range(k,r,-1):
        out=defaultdict(Q)
        for f,p in law.items():
            for a,b in combinations(range(j),2):
                g=forest([t for i,t in enumerate(f) if i not in (a,b)] + [tree(f[a],f[b])])
                out[g]+=p/Q(comb(j,2))
        law=dict(out)
    return law

@lru_cache(None)
def death_polynomial(k:int,r:int) -> dict[int,Q]:
    """P(k ancestors -> r) = sum coeff[e] x**e, x=exp(-length)."""
    if k == 0:
        return {0:Q(1)} if r == 0 else {}
    if not 1 <= r <= k:
        return {}
    lam={j:comb(j,2) for j in range(r,k+1)}
    pref=1
    for j in range(r+1,k+1):
        pref*=comb(j,2)
    ans={}
    for j in range(r,k+1):
        den=1
        for l in range(r,k+1):
            if l != j:
                den*=lam[l]-lam[j]
        ans[lam[j]]=Q(pref,den)
    return ans

@lru_cache(None)
def edge_polynomials(k:int) -> dict[Forest,dict[int,Q]]:
    if k == 0:
        return {():{0:Q(1)}}
    ans={}
    for r in range(1,k+1):
        for f,p in embedded_merger_law(k,r).items():
            ans[f]={e:p*c for e,c in death_polynomial(k,r).items() if c}
    return ans

@lru_cache(None)
def edge_law(k:int,x:Q) -> dict[Forest,Q]:
    if not Q(0) <= x <= Q(1):
        raise ValueError('Pair survival must be in [0,1].')
    ans={f:sum((c*x**e for e,c in p.items()),Q(0)) for f,p in edge_polynomials(k).items()}
    if any(p<0 for p in ans.values()) or sum(ans.values(),Q(0)) != 1:
        raise ArithmeticError('Invalid exact Kingman row.')
    return {f:p for f,p in ans.items() if p}

@lru_cache(None)
def bigon_law(k:int,x:Q,y:Q,g:Q,mode:str) -> dict[Forest,Q]:
    if mode not in ('common','independent'):
        raise ValueError('Unknown inheritance mode.')
    if not Q(0) <= g <= Q(1):
        raise ValueError('Inheritance weight must be in [0,1].')
    ans=defaultdict(Q)
    if mode == 'common':
        for z,w in ((x,g),(y,1-g)):
            for f,p in edge_law(k,z).items():
                ans[f]+=w*p
    else:
        labels=tuple(range(k))
        for bits in product((0,1),repeat=k):
            aa=tuple(i for i in labels if bits[i]==0)
            bb=tuple(i for i in labels if bits[i]==1)
            w=g**len(aa)*(1-g)**len(bb)
            for a,pa in edge_law(len(aa),x).items():
                a=tuple(relabel(t,dict(enumerate(aa))) for t in a)
                for b,pb in edge_law(len(bb),y).items():
                    b=tuple(relabel(t,dict(enumerate(bb))) for t in b)
                    ans[forest(a+b)]+=w*pa*pb
    if sum(ans.values(),Q(0)) != 1 or any(p<0 for p in ans.values()):
        raise ArithmeticError('Invalid exact bigon row.')
    return {f:p for f,p in ans.items() if p}

def poly_add(p:Poly,key:tuple[int,...],v:Q) -> None:
    p[key]=p.get(key,Q(0))+v
    if not p[key]:
        del p[key]

class Span:
    """Rational row echelon basis retaining original, physically valid rows."""
    def __init__(self,dim:int):
        self.dim=dim
        self.rows:dict[int,tuple[Q,...]]={}
        self.original:list[tuple[Q,...]]=[]
        self.witnesses:list[Any]=[]
    def reduce(self,v:Iterable[Q]) -> tuple[Q,...]:
        a=list(v)
        if len(a)!=self.dim:
            raise ValueError('Vector dimension mismatch.')
        for p,b in sorted(self.rows.items()):
            if a[p]:
                c=a[p]
                a=[x-c*y for x,y in zip(a,b)]
        return tuple(a)
    def add(self,v:Iterable[Q],witness:Any=None) -> bool:
        original=tuple(v)
        a=self.reduce(original)
        p=next((i for i,x in enumerate(a) if x),None)
        if p is None:
            return False
        self.rows[p]=tuple(x/a[p] for x in a)
        self.original.append(original)
        self.witnesses.append(witness)
        return True
    def contains(self,v:Iterable[Q]) -> bool:
        return not any(self.reduce(v))
    def __len__(self) -> int:
        return len(self.original)

class ForestAlgebra:
    def __init__(self,m:int):
        if not isinstance(m,int) or m<0:
            raise ValueError('The copy cap must be a nonnegative integer.')
        self.m=m
        self.coords=[(k,f) for k in range(m+1) for f in forests(tuple(range(k)))]
        self.index={c:i for i,c in enumerate(self.coords)}
        self.dim=len(self.coords)
        self.unit=tuple(Q(f==tuple(range(k))) for k,f in self.coords)
        self.table=[]
        for k,u in self.coords:
            i=self.index[k,u]
            for v in forests(tuple(range(len(u)))):
                j=self.index[len(u),v]
                z=self.index[k,graft(u,v)]
                self.table.append((i,j,z))
    def mul(self,a:tuple[Q,...],b:tuple[Q,...]) -> tuple[Q,...]:
        if len(a)!=self.dim or len(b)!=self.dim:
            raise ValueError('Wrong algebra dimension.')
        c=[Q(0)]*self.dim
        for i,j,z in self.table:
            if a[i] and b[j]:
                c[z]+=a[i]*b[j]
        return tuple(c)
    def edge(self,x:Q) -> tuple[Q,...]:
        return tuple(edge_law(k,x).get(f,Q(0)) for k,f in self.coords)
    def bigon(self,x:Q,y:Q,g:Q,mode:str) -> tuple[Q,...]:
        return tuple(bigon_law(k,x,y,g,mode).get(f,Q(0)) for k,f in self.coords)
    def cell(self,x:Q,y:Q,g:Q,a:Q,mode:str) -> tuple[Q,...]:
        return self.mul(self.bigon(x,y,g,mode),self.edge(a))
    def cell_polynomials(self,mode:str) -> list[Poly]:
        """Exact polynomials in x,y,g,a.  No interpolation assumption in this code."""
        if mode not in ('common','independent'):
            raise ValueError(mode)
        bs=[{} for _ in self.coords]
        for k in range(self.m+1):
            if mode == 'common':
                for f,p in edge_polynomials(k).items():
                    z=self.index[k,f]
                    for e,c in p.items():
                        poly_add(bs[z],(e,0,1,0),c)
                        poly_add(bs[z],(0,e,0,0),c)
                        poly_add(bs[z],(0,e,1,0),-c)
            else:
                for bits in product((0,1),repeat=k):
                    aa=tuple(i for i in range(k) if bits[i]==0)
                    bb=tuple(i for i in range(k) if bits[i]==1)
                    for fa,pa in edge_polynomials(len(aa)).items():
                        fa=tuple(relabel(t,dict(enumerate(aa))) for t in fa)
                        for fb,pb in edge_polynomials(len(bb)).items():
                            fb=tuple(relabel(t,dict(enumerate(bb))) for t in fb)
                            z=self.index[k,forest(fa+fb)]
                            for ex,cx in pa.items():
                                for ey,cy in pb.items():
                                    for j in range(len(bb)+1):
                                        poly_add(bs[z],(ex,ey,len(aa)+j,0),cx*cy*Q((-1)**j*comb(len(bb),j)))
        es=[edge_polynomials(k)[f] for k,f in self.coords]
        out=[{} for _ in self.coords]
        for i,j,z in self.table:
            for (ex,ey,eg,_),c in bs[i].items():
                for ea,d in es[j].items():
                    poly_add(out[z],(ex,ey,eg,ea),c*d)
        return out

    @staticmethod
    def evaluate(polys:list[Poly],args:tuple[Q,...]) -> tuple[Q,...]:
        return tuple(sum((c*prod_q(z**e for z,e in zip(args,p)) for p,c in poly.items()),Q(0)) for poly in polys)

def prod_q(xs:Iterable[Q]) -> Q:
    out=Q(1)
    for x in xs:
        out*=x
    return out

def generator_basis(alg:ForestAlgebra,modes:tuple[str,...]) -> tuple[Span,dict[str,Any]]:
    """Certify the whole polynomial generator family, using actual positive cells.

    For a paired-mode comparison, tuples share x,y,g,a. Separate mode alphabets
    would authorize different exterior experiments and are deliberately not used.
    """
    polys=[]
    for mode in modes:
        polys+=alg.cell_polynomials(mode)
    dim=alg.dim*len(modes)
    coefficients=defaultdict(lambda:[Q(0)]*dim)
    for i,p in enumerate(polys):
        for monomial,c in p.items():
            coefficients[monomial][i]=c
    coefficient_span=Span(dim)
    for c in coefficients.values():
        coefficient_span.add(c)
    actual=Span(dim)
    deg=comb(alg.m,2)
    survival_grid=tuple(Q(j,deg+2) for j in range(1,deg+2))
    inheritance_grid=tuple(Q(j,alg.m+2) for j in range(1,alg.m+2))
    visited=0
    for x,y,g,a in product(survival_grid,survival_grid,inheritance_grid,survival_grid):
        visited+=1
        args=(x,y,g,a)
        v=alg.evaluate(polys,args)
        actual.add(v,args)
        if len(actual)==len(coefficient_span):
            break
    if len(actual)!=len(coefficient_span):
        raise AssertionError('The complete interpolation grid failed to span.')
    if not all(actual.contains(c) for c in coefficients.values()):
        raise AssertionError('A polynomial coefficient escapes the legal generator span.')
    return actual,{'coefficient_rank':len(coefficient_span), 'monomial_count':len(coefficients), 'positive_grid_points_examined':visited, 'full_grid_size':len(survival_grid)**3*len(inheritance_grid)}

def algebra_basis(alg:ForestAlgebra,modes:tuple[str,...]) -> tuple[Span,dict[str,Any]]:
    gs,receipt=generator_basis(alg,modes)
    dim=alg.dim*len(modes)
    basis=Span(dim)
    basis.add(alg.unit*len(modes),())
    def mul(a,b):
        return tuple(v for i in range(len(modes)) for v in alg.mul(a[i*alg.dim:(i+1)*alg.dim],b[i*alg.dim:(i+1)*alg.dim]))
    cursor=0
    while cursor<len(basis):
        a=basis.original[cursor]
        word=basis.witnesses[cursor]
        cursor+=1
        for j,g in enumerate(gs.original):
            basis.add(mul(a,g),word+(j,))
    closure_checks=0
    for a in basis.original:
        for g in gs.original:
            if not basis.contains(mul(a,g)):
                raise AssertionError('An admitted generator escapes the final span.')
            closure_checks+=1
    receipt.update({'cap':alg.m, 'modes':list(modes), 'ambient_dimension':dim, 'algebra_rank':len(basis), 'maximum_basis_word_length':max(map(len,basis.witnesses)), 'closure_checks':closure_checks,
        'positive_generator_witnesses':[[str(x) for x in a] for a in gs.witnesses], 'word_witnesses':[list(w) for w in basis.witnesses]})
    return basis,receipt

if __name__=='__main__':
    import argparse,json
    p=argparse.ArgumentParser()
    p.add_argument('--cap',type=int,default=3)
    p.add_argument('--mode',choices=['common','independent','paired'],default='independent')
    p.add_argument('--output')
    args=p.parse_args()
    modes=('common','independent') if args.mode=='paired' else (args.mode,)
    alg=ForestAlgebra(args.cap)
    _,r=algebra_basis(alg,modes)
    text=json.dumps(r,indent=2)
    if args.output:
        with open(args.output,'w') as f:f.write(text+'\n')
    print(text)
