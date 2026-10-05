"""Working exact source-algebra probe, not an all-word sign certificate.

Exchangeable coordinates retain probability PER labelled representative.
Compression is lossless only on the natural exchangeable source subalgebra.
"""
from pathlib import Path
import sys, json, hashlib
from collections import defaultdict, Counter
from fractions import Fraction as Q
from functools import lru_cache
from math import comb
from itertools import product

PROVIDER=Path(__file__).resolve().parents[1]/'graph-g3-three-cell-return-public-20261004-1959z/reproducible-controls'
sys.path.insert(0,str(PROVIDER))
import forest_algebra_pinned as F
assert hashlib.sha256((PROVIDER/'forest_algebra_pinned.py').read_bytes()).hexdigest()=='850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884'

@lru_cache(None)
def ts(t):
    if isinstance(t,int): return 'o'
    return '('+''.join(sorted((ts(t[0]),ts(t[1]))))+')'
def fs(f): return '|'.join(sorted(map(ts,f)))

class Algebra:
    def __init__(self,m):
        self.m=m
        self.full={k:F.forests(tuple(range(k))) for k in range(m+1)}
        self.reps={};self.mult=Counter()
        for k,ff in self.full.items():
            for f in ff:
                c=(k,fs(f));self.reps.setdefault(c,f);self.mult[c]+=1
        self.coords=sorted(self.reps);self.ix={c:i for i,c in enumerate(self.coords)};self.d=len(self.coords)
        self.unit=tuple(Q(f==tuple(range(k))) for (k,s),f in self.reps_sorted())
        tab=Counter()
        for k,ff in self.full.items():
            for f in ff:
                i=self.ix[k,fs(f)]
                for h in self.full[len(f)]:
                    j=self.ix[len(f),fs(h)]
                    c=(k,fs(F.graft(f,h)));z=self.ix[c]
                    tab[i,j,z]+=1
        self.tab=[(i,j,z,Q(c,self.mult[self.coords[z]])) for (i,j,z),c in sorted(tab.items())]
    def reps_sorted(self):return [(c,self.reps[c]) for c in self.coords]
    def mul(self,a,b):
        out=[Q(0)]*self.d
        for i,j,k,c in self.tab:
            if a[i] and b[j]:out[k]+=c*a[i]*b[j]
        return tuple(out)
    def add(self,a,b):return tuple(x+y for x,y in zip(a,b))
    def scale(self,c,a):return tuple(c*x for x in a)
    def edge(self,x):return tuple(sum(c*x**e for e,c in F.edge_polynomials(k)[f].items()) for (k,s),f in self.reps_sorted())
    def idem(self,r):
        lam=comb(r,2)
        return tuple(F.edge_polynomials(k)[f].get(lam,Q(0)) for (k,s),f in self.reps_sorted())
    def bigon(self,x,y,g):return tuple(F.bigon_law(k,x,y,g,'independent').get(f,Q(0)) for (k,s),f in self.reps_sorted())
    def block(self,a,k,r):return self.mul(self.mul(self.idem(k),a),self.idem(r))
    def bigon_polys(self):
        """Uniform polynomial construction, then lossless shape compression."""
        accum=[defaultdict(Q) for _ in self.coords]
        for k in range(self.m+1):
            labels=tuple(range(k))
            for bits in product((0,1),repeat=k):
                aa=tuple(i for i in labels if bits[i]==0);bb=tuple(i for i in labels if bits[i]==1)
                for fa,pa in F.edge_polynomials(len(aa)).items():
                    la=tuple(F.relabel(t,dict(enumerate(aa))) for t in fa)
                    for fb,pb in F.edge_polynomials(len(bb)).items():
                        lb=tuple(F.relabel(t,dict(enumerate(bb))) for t in fb)
                        f=F.forest(la+lb);z=self.ix[k,fs(f)]
                        for ex,cx in pa.items():
                            for ey,cy in pb.items():
                                for j in range(len(bb)+1):
                                    accum[z][ex,ey,len(aa)+j]+=cx*cy*Q((-1)**j*comb(len(bb),j))
        return [{p:c/self.mult[self.coords[z]] for p,c in a.items() if c} for z,a in enumerate(accum)]

def main():
    a=Algebra(6);print('algebra',a.d,len(a.tab),flush=True)
    zero=tuple(Q(0) for _ in a.coords)
    ee=[a.idem(r) for r in range(1,7)]
    assert tuple(map(sum,zip(*ee)))==a.unit
    for i,e in enumerate(ee):
        for j,f in enumerate(ee):assert a.mul(e,f)==(e if i==j else zero)
    for x,y in [(Q(1,2),Q(2,3)),(Q(3,4),Q(1,5))]:assert a.mul(a.edge(x),a.edge(y))==a.edge(x*y)
    p=a.bigon_polys();print('polynomials',sum(map(len,p)),flush=True)
    mons=sorted(set().union(*(set(x) for x in p)))
    coeff=[tuple(q.get(mon,Q(0)) for q in p) for mon in mons]
    dims={};bases={}
    for k in range(2,7):
        for r in range(1,k):
            sp=F.Span(a.d)
            for c in coeff:sp.add(a.block(c,k,r))
            if len(sp):dims[f'{k},{r}']=len(sp);bases[k,r]=sp.original
    print('single-cell block dimensions',dims,flush=True)
    b64=bases.get((6,4),[]);b42=bases.get((4,2),[])
    sp=F.Span(a.d)
    for x in b64:
        for y in b42:sp.add(a.mul(x,y))
    result={'status':'WORKING_EXACT_SOURCE_ALGEBRA_CONTROLS_ONLY','cap':6,'exchangeable_coordinates':a.d,'full_labelled_coordinates':sum(map(len,a.full.values())),'table_terms':len(a.tab),'monomials':len(mons),'single_cell_block_dimensions':dims,'product_64_42_dimension':len(sp),'interpretation':'No universal sign, positive return or arbitrary-cap theorem is inferred.'}
    for x,y,g in [(Q(1,2),Q(2,3),Q(1,3)),(Q(3,5),Q(1,4),Q(2,5))]:
        v=tuple(sum(c*x**i*y**j*g**k for (i,j,k),c in q.items()) for q in p)
        assert v==a.bigon(x,y,g)
    Path(__file__).with_name('FIRST-COMPOSABLE-BLOCK-CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
    import pickle
    Path(__file__).with_name('first-composable-working-cache.pkl').write_bytes(pickle.dumps({'coords':a.coords,'table':a.tab,'polys':p,'bases':bases,'product_basis':sp.original}))
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
