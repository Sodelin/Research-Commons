from exact_small_nmsc import *

def prune(t,keep):
    if isinstance(t,str):return t if t in keep else None
    a=prune(t[0],keep);b=prune(t[1],keep)
    if a is None:return b
    if b is None:return a
    return join(a,b)

def restrict(dist,keep):
    out=defaultdict(F)
    for t,p in dist.items():out[prune(parse_tree(t),keep)]+=p
    return dict(out)
checks=[]
s=F(2,3)
p=dict(edge(('a','b'),s));assert p[('a','b')]==s and p[('(a,b)',)]==1-s
checks.append('Two-root edge formula')
p=dict(edge(('a','b','c'),s));assert p[('a','b','c')]==s**3
assert p[('(a,b)','c')]==(s-s**3)/2
assert p[('((a,b),c)',)]==F(1,3)-s/2+s**3/6
checks.append('Three-root no/one/two-merger formulas')
es=[('R','U'),('R','V'),('U','A'),('U','B'),('V','C'),('V','D')]
pars={}
for a,b in es:pars.setdefault(b,[]).append(a)
tree=(list('ABCD')+['U','V','R'],pars,{e:F(1,2) for e in es},{})
u=unroot(run(tree,{x:1 for x in 'ABCD'}));assert sorted(u.values())==[F(1,12),F(1,12),F(5,6)]
checks.append('Ordinary balanced quartet MSC formula')
keep={x+'0' for x in 'ABCD'}
for name,source in [('triangle',triangle(F(9,10))),('fourcycle',fourcycle())]:
    base=run(source,{x:1 for x in 'ABCD'})
    for duplicated in 'ABCD':
        alloc={x:1 for x in 'ABCD'};alloc[duplicated]=2
        richer=run(source,alloc)
        assert restrict(richer,keep)==base
        checks.append(name+': selected-label rooted projectivity with duplicated '+duplicated)
# Rooted caterpillar normalization at infinite ancestral population.
assert len(dict(ancestral(('a','b','c','d'))))==15
assert sum(dict(ancestral(('a','b','c','d'))).values())==1
checks.append('Four-root ancestral normalization and topology count')
print(json.dumps({'status':'Executed exact local tests, not independent implementation validation','passed':len(checks),'checks':checks},indent=2))
