"""Frozen source certificates for the conditional fifth-order guard; exact rationals."""
from pathlib import Path
from fractions import Fraction as F
from itertools import combinations
from math import comb
import hashlib,json,types
BASE=Path(__file__).resolve().parent
PROVIDER=BASE.parent/'g4-coherent-sixth-jet-20261005-2058z/source_coefficients.py'
PIN='aed745dd0d3fc37a8b5eef838f000675ad3fb6c37a66116f14eacfe01192f998'
CORE=BASE.parent/'g4-lossless-resonance-20261005-2042z/lossless_resonance.py'
CORE_PIN='3bbbbe54d4c28abe2515c14143e9d83629e650ba0ac0df411457dec7fa17c9be'
def load(path,pin,name):
    if path.is_symlink():raise ValueError('provider symlink')
    raw=path.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=pin:raise ValueError('provider hash')
    mod=types.ModuleType(name);mod.__file__=str(path);exec(compile(raw,str(path),'exec'),mod.__dict__);return mod
if CORE.is_symlink() or hashlib.sha256(CORE.read_bytes()).hexdigest()!=CORE_PIN:raise ValueError('core pin')
c=load(PROVIDER,PIN,'_fifth_source_provider');m=c.m
NAMES=['R','adQ_R','adQ2_R','adQ3_R','B4','adQ_B4','adQ2_B4']

def build_ten():
    # Exact accepted complete-forest definition, with only the declared cap extended to10.
    states=tuple(sorted(m.forests(10),key=lambda f:(len(f),f)));ids={f:i for i,f in enumerate(states)};q=[];r=[]
    for f in states:
        k=len(f);qi={ids[f]:F(-comb(k,2))};ri={ids[f]:F(2*comb(k,3))}
        def add(d,ff,v):
            i=ids[tuple(sorted(ff))];d[i]=d.get(i,F(0))+v
        for i,j in combinations(range(k),2):
            ff=[m.tree(f[i],f[j])]+[f[h] for h in range(k) if h not in (i,j)]
            add(qi,ff,F(1));add(ri,ff,F(-(k-2)))
        for i,j,l in combinations(range(k),3):
            rest=[f[h] for h in range(k) if h not in (i,j,l)]
            for x,y,z in ((i,j,l),(i,l,j),(j,l,i)):add(ri,[m.tree(m.tree(f[x],f[y]),f[z])]+rest,F(1,3))
        if sum(qi.values()) or sum(ri.values()):raise ValueError('generator row sum')
        q.append({i:v for i,v in qi.items() if v});r.append({i:v for i,v in ri.items() if v})
    return states,ids,q,r

def coloured_ten():
    states=tuple((a,b) for k in range(11) for a in m.forests(k) for b in m.forests(10-k));ids={v:i for i,v in enumerate(states)};qs=[]
    if len(states)>4096:raise ValueError('coloured state ceiling')
    for side in (0,1):
        mat=[]
        for a,b in states:
            f=(a,b)[side];row={ids[a,b]:F(-comb(len(f),2))}
            for i,j in combinations(range(len(f)),2):
                ff=tuple(sorted([m.tree(f[i],f[j])]+[f[k] for k in range(len(f)) if k not in (i,j)]));state=(ff,b) if side==0 else (a,ff);h=ids[state];row[h]=row.get(h,F(0))+1
            if sum(row.values()):raise ValueError('coloured row sum')
            mat.append({i:v for i,v in row.items() if v})
        qs.append(mat)
    return states,ids,*qs

def positive_binomial(row,q,l):
    out=list(row)
    for k in range(l):out=[(x-k*y)/(k+1) for x,y in zip(m.apply(out,q),out)]
    return out

def kappa(r,s,j):return sum(comb(r,i)*comb(s,2*j-i)*(-1)**(2*j-i) for i in range(r+1) if 0<=2*j-i<=s)

class Context:
    def __init__(self,n):
        if not 0<=n<=10:raise ValueError('frozen arity range')
        self.n=n
        if n==0:
            self.states=((),);self.ids={():0};self.q=self.r=[{}]
            self.colours=(((),()),);self.cids={((),()):0};self.ql=self.qr=[{}]
        elif n==10:
            self.states,self.ids,self.q,self.r=build_ten();self.colours,self.cids,self.ql,self.qr=coloured_ten()
        else:
            self.states,self.ids,self.q,self.r=m.build(n);self.colours,self.cids,self.ql,self.qr=c.coloured(n)
        if len(self.states)>2000 or len(self.colours)>4096:raise ValueError('state ceiling')
        self.e=[F(0)]*len(self.states);self.e[self.ids[('x',)*n]]=F(1)
        self.cache={};self.hcache={}
    def arms(self,v):
        key=tuple(v)
        if key in self.cache:return self.cache[key]
        ans={};left=c.split(v,self.states,self.cids)
        for r in range(6):
            row=left
            for s in range(6-r):
                raw=[F(0)]*len(self.states)
                for value,(a,b) in zip(row,self.colours):raw[self.ids[tuple(sorted(a+b))]]+=value
                ans[r,s]=raw
                if s<5-r:row=c.binomial_next(row,self.qr,s)
            if r<5:left=c.binomial_next(left,self.ql,r)
        self.cache[key]=ans;return ans
    def H(self,d,j,v):
        if d not in (4,5) or j not in (0,1):raise ValueError('frozen coefficients')
        key=(d,j,tuple(v))
        if key in self.hcache:return self.hcache[key]
        arms=self.arms(v);out=[F(0)]*len(v)
        for l in range(d-3*j+1):
            k=d-j-l
            for r in range(k+1):
                s=k-r;factor=F((-1)**(d-j)*kappa(r,s,j),2**l)
                if factor:out=[x+factor*y for x,y in zip(out,positive_binomial(arms[r,s],self.q,l))]
        self.hcache[key]=out;return out
    def actor(self,name,v):
        if name=='R':return m.apply(v,self.r)
        if name=='B4':return [F(8,3)*x for x in self.H(4,1,v)]
        if name=='B5':return [F(8,3)*x for x in self.H(5,1,v)]
        if name=='A5':return [x+y/6 for x,y in zip(self.H(5,0,v),self.H(5,1,v))]
        raise ValueError('actor')
    def ad(self,name,k,v):
        if not 0<=k<=3:raise ValueError('commutator degree')
        out=[F(0)]*len(v)
        for i in range(k+1):
            left=list(v)
            for _ in range(k-i):left=m.apply(left,self.q)
            row=self.actor(name,left)
            for _ in range(i):row=m.apply(row,self.q)
            out=[x+(-1)**i*comb(k,i)*y for x,y in zip(out,row)]
        return out
    def certificate_rows(self):
        cols=[self.ad('R',k,self.e) for k in range(4)]+[self.ad('B4',k,self.e) for k in range(3)]
        a=self.actor('A5',self.e);d=self.actor('B5',self.e);ad=self.ad('B5',1,self.e)
        target=[x-(30*y+z)/1200 for x,y,z in zip(a,d,ad)]
        return cols,target

def determinant(rows):
    a=[list(r) for r in rows];n=len(a)
    if any(len(r)!=n for r in a):raise ValueError('square determinant')
    value=F(1)
    for j in range(n):
        k=next((k for k in range(j,n) if a[k][j]),None)
        if k is None:return F(0)
        if k!=j:a[k],a[j]=a[j],a[k];value=-value
        p=a[j][j];value*=p
        for i in range(j+1,n):
            factor=a[i][j]/p
            for h in range(j+1,n):a[i][h]-=factor*a[j][h]
            a[i][j]=F(0)
    return value

def independent_indices(vectors):
    chosen=[];rows=[]
    for i,v in enumerate(vectors):
        if m.rank(rows+[v])>len(rows):chosen.append(i);rows.append(v)
    return chosen

def run():
    columns=[[] for _ in NAMES];target=[];records=[];coordinates=[]
    for n in range(11):
        ctx=Context(n);cols,t=ctx.certificate_rows()
        for dst,v in zip(columns,cols):dst.extend(v)
        target.extend(t)
        coordinates.extend({'arity':n,'orbit_index':i} for i in range(len(t)))
        records.append({'arity':n,'orbit_count':len(ctx.states),'two_colour_count':len(ctx.colours),'orbits':[{'shape':list(f),'labelled_multiplicity':m.orbit_size(f)} for f in ctx.states],
                        'lower_columns':{name:list(map(str,v)) for name,v in zip(NAMES,cols)},'unchanged_residual':list(map(str,t))})
    coeff=m.relation(columns,target)
    out={'schema':'fifth-source-guard-premises-v1','provider_sha256':PIN,'forest_sha256':CORE_PIN,'fixed_lower_basis':NAMES,'fixed_residual':'A5-(30B5+[Q,B5])/1200','all_arity_support_bound':10,'records':records,'P1_coefficients':None if coeff is None else list(map(str,coeff)),'P2':None,'original_G4_closed':False,'arbitrary_rival_obstruction':False}
    if coeff is None:
        chosen=independent_indices(columns);selected=[columns[i] for i in chosen]
        aug=selected+[target];rows=list(zip(*aug));rowids=independent_indices(rows)
        if len(rowids)!=len(chosen)+1:raise ValueError('negative membership certificate')
        mat=[list(rows[i]) for i in rowids];det=determinant(mat)
        if not det:raise ValueError('zero separating minor')
        omitted={NAMES[i]:list(map(str,m.relation(selected,columns[i]))) for i in range(len(NAMES)) if i not in chosen}
        out.update({'decision':'P1_FALSE_IN_FROZEN_UNIVERSAL_SPAN','conditional_guard_premises_discharged':False,'P1_nonmembership_certificate':{'independent_lower_names':[NAMES[i] for i in chosen],'other_lower_relations':omitted,'row_coordinates':[coordinates[i] for i in rowids],'matrix':[[str(x) for x in r] for r in mat],'determinant':str(det)},'P2_not_executed_reason':'P1 failed; frozen stopping rule'})
        return out
    if any(sum(x*v for x,v in zip(coeff,row))!=t for row,t in zip(zip(*columns),target)):raise ValueError('membership verification')
    ctx=Context(9);left=m.project(ctx.e,9,ctx.q,9)
    block=[m.project(ctx.actor(name,left),4,ctx.q,9) for name in ('R','B4','B5')]
    top=[i for i,f in enumerate(ctx.states) if len(f)==4]
    perlabel=[[v[i]/m.orbit_size(ctx.states[i]) for v in block] for i in top]
    chosen=independent_indices(perlabel)
    p2={'arity':9,'output_current_roots':4,'column_names':['R','B4','B5'],'all_top_orbit_indices':top,'all_top_shapes':[list(ctx.states[i]) for i in top],'all_labelled_coefficients':[[str(x) for x in row] for row in perlabel],'rank':len(chosen)}
    if len(chosen)==3:
        mat=[perlabel[i] for i in chosen];det=determinant(mat)
        if not det:raise ValueError('P2 minor')
        p2.update({'minor_top_row_indices':chosen,'minor_shapes':[list(ctx.states[top[i]]) for i in chosen],'minor_matrix':[[str(x) for x in row] for row in mat],'minor_determinant':str(det)})
    out['P2']=p2;out['conditional_guard_premises_discharged']=len(chosen)==3
    out['decision']='BOTH_SOURCE_PREMISES_CERTIFIED' if len(chosen)==3 else 'P2_FIXED_NINE_RANK_PREMISE_FALSE'
    return out
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
