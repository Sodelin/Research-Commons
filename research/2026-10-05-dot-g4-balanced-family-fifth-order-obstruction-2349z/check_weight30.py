"""Exact complete weight-30 fifth-source cone; monotone quotients, no new-weight search."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import comb
import hashlib,types,json
BASE=Path(__file__).resolve().parent
HELPER=BASE.parent/'g4-fifth-source-cone-20261005-2246z/check_source_premises.py'
HELPER_PIN='51c876c74fe53ba198aadcd6179f8eb7e0669ae59914459b5417485f21d9ab17'
def load(path,pin,name):
    if path.is_symlink():raise ValueError('helper symlink')
    raw=path.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=pin:raise ValueError('helper hash')
    mod=types.ModuleType(name);mod.__file__=str(path);exec(compile(raw,str(path),'exec'),mod.__dict__);return mod
h=load(HELPER,HELPER_PIN,'_weight30_arithmetic_provider');m=h.m;c=h.c
CASES=((9,4),(10,6),(12,9))
class Quotient:
    def __init__(self,n,bottom):
        if not 1<=bottom<=n<=12:raise ValueError('frozen root-count domain')
        self.n=n;self.bottom=bottom
        self.states=tuple(sorted((f for f in m.forests(n) if len(f)>=bottom),key=lambda f:(len(f),f)));self.ids={f:i for i,f in enumerate(self.states)}
        if len(self.states)>2000:raise ValueError('complete state ceiling')
        self.q=[];self.r=[]
        for f in self.states:
            k=len(f);qr={self.ids[f]:F(-comb(k,2))};rr={self.ids[f]:F(2*comb(k,3))}
            def add(dst,ff,value):
                ff=tuple(sorted(ff))
                if len(ff)<bottom:return
                i=self.ids[ff];dst[i]=dst.get(i,F(0))+value
            for i,j in combinations(range(k),2):
                ff=[m.tree(f[i],f[j])]+[f[a] for a in range(k) if a not in (i,j)]
                add(qr,ff,F(1));add(rr,ff,F(-(k-2)))
            for i,j,l in combinations(range(k),3):
                rest=[f[a] for a in range(k) if a not in (i,j,l)]
                for x,y,z in ((i,j,l),(i,l,j),(j,l,i)):add(rr,[m.tree(m.tree(f[x],f[y]),f[z])]+rest,F(1,3))
            if sum(qr.values())!=(-comb(k,2) if k==bottom else 0):raise ValueError('ordinary quotient diagonal')
            expected=2*comb(k,3) if k==bottom else (-comb(k,3) if k==bottom+1 else 0)
            if sum(rr.values())!=expected:raise ValueError('triple quotient diagonal')
            self.q.append({i:v for i,v in qr.items() if v});self.r.append({i:v for i,v in rr.items() if v})
        self.colours=tuple((a,b) for k in range(n+1) for a in m.forests(k) for b in m.forests(n-k) if len(a)+len(b)>=bottom)
        self.cids={f:i for i,f in enumerate(self.colours)}
        if len(self.colours)>4096:raise ValueError('colour state ceiling')
        mats=[]
        for side in (0,1):
            mat=[]
            for a,b in self.colours:
                f=(a,b)[side];total=len(a)+len(b);rate=comb(len(f),2);row={self.cids[a,b]:F(-rate)}
                for i,j in combinations(range(len(f)),2):
                    ff=tuple(sorted([m.tree(f[i],f[j])]+[f[k] for k in range(len(f)) if k not in (i,j)]));state=(ff,b) if side==0 else (a,ff)
                    if total-1<bottom:continue
                    k=self.cids[state];row[k]=row.get(k,F(0))+1
                if sum(row.values())!=(-rate if total==bottom else 0):raise ValueError('colour quotient diagonal')
                mat.append({i:v for i,v in row.items() if v})
            mats.append(mat)
        self.ql,self.qr=mats;self.cache={}
        self.e=[F(0)]*len(self.states);self.e[self.ids[('x',)*n]]=F(1)
    def project(self,row,j):
        if not self.bottom<=j<=self.n:raise ValueError('projector index')
        out=list(row);lj=comb(j,2)
        for k in range(self.bottom,self.n+1):
            if k!=j:
                lk=comb(k,2);out=[(x+lk*y)/(lk-lj) for x,y in zip(m.apply(out,self.q),out)]
        if m.apply(out,self.q)!=[-lj*x for x in out]:raise ValueError('projector eigenrow')
        return out
    def arms(self,v):
        key=tuple(v)
        if key in self.cache:return self.cache[key]
        ans={};left=c.split(v,self.states,self.cids)
        for r in range(6):
            row=left
            for s in range(6-r):
                out=[F(0)]*len(v)
                for value,(a,b) in zip(row,self.colours):out[self.ids[tuple(sorted(a+b))]]+=value
                ans[r,s]=out
                if s<5-r:row=c.binomial_next(row,self.qr,s)
            if r<5:left=c.binomial_next(left,self.ql,r)
        self.cache[key]=ans;return ans
    def H(self,d,j,v):
        if d not in (4,5) or j not in (0,1):raise ValueError('coefficient scope')
        out=[F(0)]*len(v);arms=self.arms(v)
        for l in range(d-3*j+1):
            k=d-j-l
            for r in range(k+1):
                s=k-r;factor=F((-1)**(d-j)*h.kappa(r,s,j),2**l)
                if factor:out=[x+factor*y for x,y in zip(out,h.positive_binomial(arms[r,s],self.q,l))]
        return out
    def actor(self,name,v):
        if name=='R':return m.apply(v,self.r)
        if name=='B4':return [F(8,3)*x for x in self.H(4,1,v)]
        if name=='D5':return [F(8,3)*x for x in self.H(5,1,v)]
        if name=='A5':return [x+y/6 for x,y in zip(self.H(5,0,v),self.H(5,1,v))]
        raise ValueError('actor')
    def block(self):
        left=self.project(self.e,self.n);rows={name:self.project(self.actor(name,left),self.bottom) for name in ('R','B4','A5','D5')}
        if rows['B4']!=[-F(25,2)*x for x in rows['R']]:raise ValueError('accepted weight30 lower relation')
        top=[i for i,f in enumerate(self.states) if len(f)==self.bottom]
        return top,rows

def prior_phi_check(ctx,top,rows):
    if (ctx.n,ctx.bottom)!=(9,4):raise ValueError('prior check scope')
    full,ids,q,_=m.build(9);values={}
    for name in ('R','A5','D5'):
        seed=[F(0)]*len(full)
        for i in top:seed[ids[ctx.states[i]]]=rows[name][i]
        extended=m.project(seed,4,q,9)
        values[name]=sum(F(w)*extended[i] for i,w in enumerate((245,146,68)))
    if values!={'R':F(0),'A5':F(0),'D5':F(84)}:raise ValueError('accepted prior functional mismatch')
    return {k:str(v) for k,v in values.items()}

def run():
    records=[];coordinates=[];columns={name:[] for name in ('R','A5','D5')};prior=None
    for n,j in CASES:
        ctx=Quotient(n,j);top,rows=ctx.block()
        if n==9:prior=prior_phi_check(ctx,top,rows)
        labelled={name:[rows[name][i]/m.orbit_size(ctx.states[i]) for i in top] for name in columns}
        for name in columns:columns[name].extend(labelled[name])
        coordinates.extend({'input_arity':n,'output_root_count':j,'top_orbit_index':k,'shape':list(ctx.states[i]),'labelled_multiplicity':m.orbit_size(ctx.states[i])} for k,i in enumerate(top))
        records.append({'input_arity':n,'output_root_count':j,'weight':comb(n,2)-comb(j,2),'quotient_orbit_count':len(ctx.states),'quotient_colour_count':len(ctx.colours),'top_shapes':[list(ctx.states[i]) for i in top],'top_multiplicities':[m.orbit_size(ctx.states[i]) for i in top],'per_labelled_coefficients':{name:list(map(str,v)) for name,v in labelled.items()},'lower_B4_relation_verified':True})
    if m.rank([columns['R'],columns['D5']])!=2:raise ValueError('prior lower rank not reproduced')
    rank=m.rank(list(columns.values()));out={'schema':'complete-weight30-source-cone-v1','arithmetic_provider_sha256':HELPER_PIN,'blocks':records,'prior_functional':prior,'complete_weight_rank':rank,'one_pair_block_31_30_zero_by_projectivity':True,'original_G4_closed':False,'other_weights_examined':False}
    if rank==3:
        rowvectors=list(zip(*columns.values()));selected=h.independent_indices(rowvectors)
        if len(selected)!=3:raise ValueError('minor selection')
        matrix=[list(rowvectors[i]) for i in selected];det=h.determinant(matrix)
        weights=m.relation(matrix,[F(0),F(1),F(1)])
        if not det or weights is None or [sum(w*row[k] for w,row in zip(weights,matrix)) for k in range(3)]!=[F(0),F(1),F(1)]:raise ValueError('strict guard certificate')
        out.update({'decision':'STRICT_WEIGHT30_FIFTH_GUARD','guard':{'columns':['R','A5','D5'],'coordinates':[coordinates[i] for i in selected],'matrix':[[str(x) for x in row] for row in matrix],'determinant':str(det),'covector_weights':list(map(str,weights)),'values_R_A5_D5':['0','1','1'],'source_value':'a^5 exp(-30s)(1+r/a^3)>15 a^5 exp(-30s)/16'},'symmetric_weak_family_fifth_stage_excluded_at_cap_12':True})
    elif rank==2:
        relation=m.relation([columns['R'],columns['D5']],columns['A5'])
        if relation is None or relation[1]!=0:raise ValueError('rank-two prior consistency')
        out.update({'decision':'NO_NONTRIVIAL_GUARD_ON_COMPLETE_WEIGHT30','A5_coefficients_R_D5':list(map(str,relation)),'symmetric_weak_family_fifth_stage_excluded_at_cap_12':False,'whole_fifth_cone_decided':False})
    else:raise ValueError('unexpected rank')
    return out
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
