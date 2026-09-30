"""Exact local partition tomography and chronological target recovery.

This file never searches a source-graph class.  The inverse routines consume
local genealogy-derivative oracles and a certified finite calendar-cell cover.
Only the test-data routines below inspect supplied source fixtures.

Arithmetic: Fractions, with rational spectral roots in this implementation.
An unsupported root, invalid promise, or resource guard is NOT a certificate.
"""
from __future__ import annotations
from collections import defaultdict, Counter
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import factorial
from typing import Callable, Iterable, Mapping
import sympy as sp
import networkx as nx

Partition = tuple[tuple[str, ...], ...]

class Unknown(RuntimeError):
    """Computation not completed under the implementation's exact domain."""


def canonical(blocks: Iterable[Iterable[str]]) -> Partition:
    return tuple(sorted(tuple(sorted(b)) for b in blocks))


@lru_cache(None)
def partitions(labels: tuple[str, ...]) -> tuple[Partition, ...]:
    """Finite local coalescent state space, not phylogenetic source enumeration."""
    if not labels:
        return ((),)
    x, rest = labels[0], labels[1:]
    out = set()
    for p in partitions(rest):
        out.add(canonical(((x,),) + p))
        for i in range(len(p)):
            out.add(canonical(p[:i] + (p[i] + (x,),) + p[i+1:]))
    return tuple(sorted(out))


def choose2(k: int) -> int:
    return k * (k-1) // 2


def mean_coefficient(k: int, j: int) -> F:
    if not 2 <= j <= k:
        raise ValueError('Need 2 <= j <= k')
    return F((2*j-1)*factorial(k)*factorial(k-1),
             factorial(k-j)*factorial(k+j-1))


def _frac(x) -> F:
    x = sp.cancel(x)
    if not x.is_Rational:
        raise Unknown(f'Nonrational exact arithmetic/root not implemented: {x}')
    return F(int(x.p), int(x.q))


class FrozenMixture:
    """Test-data generator for exact local genealogy derivatives.

    Each component is (positive weight, ((population block, pair rate), ...)).
    Arbitrary components are permitted to TEST THE ALGEBRAIC LEMMA ONLY;
    they are not thereby claimed to have biological source realizations.
    """
    def __init__(self, labels: Iterable[str], components):
        self.labels = tuple(sorted(labels))
        self.components = []
        total = F(0)
        for weight, populations in components:
            weight = F(weight)
            if weight <= 0:
                raise ValueError('Mixture weights must be strictly positive')
            populations = tuple((tuple(sorted(b)), F(r)) for b, r in populations)
            if sorted(x for b, _ in populations for x in b) != list(self.labels) or any(not b for b,_ in populations):
                raise ValueError('Populations must partition the supplied labels')
            if any(r <= 0 for _, r in populations):
                raise ValueError('Population pair rates must be positive')
            total += weight
            self.components.append((weight, populations))
        if total != 1:
            raise ValueError('Mixture weights must sum to one')
        self._vectors = []
        self._generators = []
        self._cache = []

    def _prepare_generators(self):
        if self._generators:
            return
        self.parts = partitions(self.labels)
        initial = canonical((x,) for x in self.labels)
        for _, pops in self.components:
            pop_of = {x: i for i, (b, _) in enumerate(pops) for x in b}
            generator = {}
            for p in self.parts:
                # Only refinements of this population partition are reachable.
                if any(len({pop_of[x] for x in b}) != 1 for b in p):
                    continue
                row = defaultdict(F)
                for i, j in combinations(range(len(p)), 2):
                    a, b = p[i], p[j]
                    if pop_of[a[0]] != pop_of[b[0]]:
                        continue
                    rate = pops[pop_of[a[0]]][1]
                    q = canonical([p[k] for k in range(len(p)) if k not in (i,j)]
                                  + [a+b])
                    row[q] += rate
                    row[p] -= rate
                generator[p] = dict(row)
            self._generators.append(generator)
            self._vectors.append([{initial: F(1)}])
    def derivative(self, k: int) -> Mapping[Partition, F]:
        if k < 0:
            raise ValueError('Derivative order must be nonnegative')
        self._prepare_generators()
        while len(self._cache) <= k:
            order = len(self._cache)
            total = defaultdict(F)
            for ci, (weight, _) in enumerate(self.components):
                vv = self._vectors[ci]
                while len(vv) <= order:
                    nxt = defaultdict(F)
                    for p, val in vv[-1].items():
                        for q, rate in self._generators[ci][p].items():
                            nxt[q] += val * rate
                    vv.append({p: a for p, a in nxt.items() if a})
                for p, a in vv[order].items():
                    total[p] += weight * a
            self._cache.append({p: a for p, a in total.items() if a})
        return self._cache[k]

    def truth(self) -> dict[Partition, F]:
        out = defaultdict(F)
        for w, pops in self.components:
            out[canonical(b for b, _ in pops)] += w
        return dict(out)


def recover_occupancy(labels: Iterable[str], derivative: Callable,
                      max_atoms: int = 30, max_derivative: int = 250):
    """Recover the hidden population-partition weights from genealogy germs.

    Source promise: the supplied derivatives come from a positive finite mixture
    of frozen-epoch Kingman populations on these labels.  No atom/source-size
    bound is mathematically presumed. max_atoms/max_derivative are resource
    guards: exhaustion raises Unknown, never returns a false completed answer.
    The exact-root implementation currently accepts rational eigenrates only.
    """
    labels = tuple(sorted(labels))
    m = len(labels)
    if not m:
        raise ValueError('At least one selected taxon is required')
    moment_cache = {}
    def moment(k):
        if k > max_derivative:
            raise Unknown('Derivative resource guard exhausted')
        if k not in moment_cache:
            moment_cache[k] = (-1)**k * sum(F(a)*len(p) for p,a in derivative(k).items())
        return moment_cache[k]
    if moment(0) != m:
        raise ValueError('Initial state must consist of all selected singleton lineages')
    z = sp.Symbol('z')
    minors = []
    null = None
    for d in range(1, max_atoms+1):
        H = sp.Matrix(d+1,d+1,lambda i,j:sp.Rational(moment(i+j).numerator,
                                                    moment(i+j).denominator))
        det = H.det(method='domain-ge')
        minors.append(str(det))
        if det < 0:
            raise ValueError('Positive-moment source promise fails')
        if det == 0:
            basis = H.nullspace()
            if len(basis) != 1 or basis[0][-1] == 0:
                raise ValueError('Invalid first-singular Hankel certificate')
            null = [sp.cancel(a/basis[0][-1]) for a in basis[0]]
            break
    if null is None:
        raise Unknown('Atom-count resource guard exhausted')
    annihilating = sp.Poly(sum(a*z**i for i,a in enumerate(null)), z)
    beta = sorted({_frac(x) for x in annihilating.all_roots()})
    if len(beta) != d or beta[0] != 0 or any(x < 0 for x in beta):
        raise ValueError('Invalid finite nonnegative spectrum')
    V = sp.Matrix(d,d,lambda i,j:sp.Rational(beta[j].numerator,beta[j].denominator)**i)
    spectral_weights = [_frac(x) for x in V.inv()*sp.Matrix([moment(i) for i in range(d)])]
    if any(w <= 0 for w in spectral_weights):
        raise ValueError('Nonpositive spectral weight')
    for k in range(2*d+1):
        if sum(w*b**k for w,b in zip(spectral_weights,beta)) != moment(k):
            raise ValueError('Moment certificate replay failed')
    # A sum of at most floor(m/2) nonconstant population spectra suffices.
    positive = [b for b in beta if b]
    omega = {F(0)}
    layer = {F(0)}
    for _ in range(m//2):
        layer = {x+y for x in layer for y in positive}
        omega |= layer
    coeff = [F(1)]
    for b in sorted(omega - {F(0)}):
        nxt = [F(0)]*(len(coeff)+1)
        for i,c in enumerate(coeff):
            nxt[i] += c
            nxt[i+1] += c/b
        coeff = nxt
    if len(coeff)-1 > max_derivative:
        raise Unknown('Annihilator derivative resource guard exhausted')
    answer = defaultdict(F)
    for k,c in enumerate(coeff):
        for p,a in derivative(k).items():
            answer[p] += c*F(a)
    answer = {p:a for p,a in answer.items() if a}
    if sum(answer.values()) != 1 or any(a < 0 for a in answer.values()):
        raise ValueError('Recovered occupancy law violates probability constraints')
    certificate = {
        'spectral_atom_count': d,
        'first_singular_hankel_order': d,
        'leading_determinants_from_order_1': minors,
        'positive_spectrum': [str(b) for b in beta],
        'spectral_weights': [str(w) for w in spectral_weights],
        'annihilating_polynomial': str(annihilating.as_expr()),
        'candidate_frequency_count': len(omega),
        'highest_derivative_used': max(2*d,len(coeff)-1),
        'occupancy_weights': [{'partition':p,'weight':str(a)} for p,a in sorted(answer.items())],
        'status': 'EXACT_WITHIN_DECLARED_DERIVATIVE_ORACLE_DOMAIN'
    }
    return answer, certificate


def chronological_clusters(labels: Iterable[str], calendar_cells: Iterable[int],
                           support: Callable) -> tuple[set[frozenset[str]], list[dict]]:
    """Inverse from support-constant right-hand calendar cells and germ support.

    The callable only sees a selected label subset and cell. It must return the
    positive population partitions reconstructed from their genealogy germs.
    No network or inheritance mode is read by this routine.
    """
    labels = tuple(sorted(labels))
    active = {x:frozenset([x]) for x in labels}
    clusters = set(active.values())
    stages = []
    for t in calendar_cells:
        while len(active) > 1:
            R = tuple(sorted(active))
            pp = tuple(support(R,t))
            if not pp:
                raise ValueError('The support oracle returned an empty law')
            for p in pp:
                if canonical(p) not in partitions(R):
                    raise ValueError('Invalid selected population partition')
                for block in p:
                    clusters.add(frozenset().union(*(active[x] for x in block)))
            sure = set(pp[0]).intersection(*(set(p) for p in pp[1:]))
            sure = sorted(b for b in sure if len(b)>1)
            if not sure:
                break
            stages.append({'time_cell':t,'selected':R,'sure_blocks':sure})
            for b in sure:
                union = frozenset().union(*(active[x] for x in b))
                for x in b:
                    del active[x]
                active[min(b)] = union
                clusters.add(union)
        if len(active) == 1:
            return clusters, stages
    raise Unknown('Supplied calendar cover did not reach a sure common ancestor')


def splits_from_clusters(labels: Iterable[str], clusters) -> set[tuple[tuple[str,...],tuple[str,...]]]:
    X = frozenset(labels)
    out = set()
    for c in clusters:
        c = frozenset(c)
        d = X-c
        if len(c)>=2 and len(d)>=2:
            a,b = sorted([tuple(sorted(c)),tuple(sorted(d))])
            out.add((a,b))
    return out


def quartets_from_splits(labels: Iterable[str], splits):
    out = {q:set() for q in combinations(sorted(labels),4)}
    for q in out:
        Q = set(q)
        for a,b in splits:
            aa,bb=Q.intersection(a),Q.intersection(b)
            if len(aa)==len(bb)==2:
                out[q].add(tuple(sorted([tuple(sorted(aa)),tuple(sorted(bb))])))
    return out


# ---------- Supplied-fixture forward utilities; not used by inverse above. ----------
@dataclass(frozen=True)
class Edge:
    id: str
    parent: str
    child: str
    rate: int = 1

@dataclass
class Source:
    name: str
    ages: dict[str,int]  # calendar ages are these integers times log(2)
    labels: tuple[str,...]
    edges: list[Edge]
    inheritance: dict[str,F]
    ancestral_rate: int = 1

    def incoming(self,v):
        return [e for e in self.edges if e.child==v]
    def outgoing(self,v):
        return [e for e in self.edges if e.parent==v]
    def root(self):
        rr=[v for v in self.ages if not self.incoming(v)]
        if len(rr)!=1: raise ValueError('Unique root required')
        return rr[0]
    def cells(self):
        return sorted(set(self.ages.values()))
    def hybrids(self):
        return sorted(v for v in self.ages if len(self.incoming(v))==2)

    def validate(self):
        if len({e.id for e in self.edges})!=len(self.edges):
            raise ValueError('Duplicate population-edge IDs')
        G=nx.DiGraph()
        G.add_nodes_from(self.ages)
        G.add_edges_from((e.parent,e.child) for e in self.edges)
        if not nx.is_directed_acyclic_graph(G): raise ValueError('Non-DAG')
        root=self.root()
        for v in self.ages:
            deg=(len(self.incoming(v)),len(self.outgoing(v)))
            good=(0,2) if v==root else (1,0) if v in self.labels else None
            if good is not None and deg!=good: raise ValueError(f'Bad degree {v}: {deg}')
            if good is None and deg not in ((1,2),(2,1)):
                raise ValueError(f'Bad internal degree {v}: {deg}')
        if set(v for v in self.ages if not self.outgoing(v))!=set(self.labels):
            raise ValueError('Unlabeled leaf')
        if any(self.ages[x]!=0 for x in self.labels): raise ValueError('Noncontemporaneous tips')
        if self.ancestral_rate<=0: raise ValueError('Bad ancestral rate')
        for e in self.edges:
            if e.rate<=0 or self.ages[e.parent]<=self.ages[e.child]:
                raise ValueError('Nonpositive duration/rate')
        U=nx.MultiGraph()
        U.add_nodes_from(self.ages)
        for e in self.edges: U.add_edge(e.parent,e.child,key=e.id)
        for h in self.hybrids():
            if h not in self.inheritance or not 0<self.inheritance[h]<1:
                raise ValueError('Noninterior inheritance')
            e=self.outgoing(h)[0]
            V=U.copy();V.remove_edge(e.parent,e.child,e.id)
            if nx.has_path(V,e.parent,e.child):
                raise ValueError('Hybrid child edge is not a cut edge')
        for v in self.ages:
            if v==root: continue
            D=G.copy();D.remove_node(v)
            # A nonroot vertex is stable for all samples only if its deletion
            # leaves no sampled taxon reachable from the root.
            if all(x==v or not nx.has_path(D,root,x) for x in self.labels):
                raise ValueError('Root is not the lowest stable ancestor')
        # Stronger sufficient fixture check: all vertices outerplanar.
        O=nx.Graph(U);hub='__outer_hub__'
        O.add_node(hub);O.add_edges_from((hub,v) for v in self.ages)
        outer=nx.check_planarity(O)[0]
        if not outer: raise ValueError('Fixture does not pass sufficient outerplanarity check')
        # Cycle rank of the largest biconnected multigraph block = level here.
        # Count all parallel edges whose endpoints lie within a simple block.
        simple=nx.Graph(U)
        level=0
        for vs in nx.biconnected_components(simple):
            ec=sum(1 for e in self.edges if e.parent in vs and e.child in vs)
            level=max(level,ec-len(vs)+1)
        return {'taxa':len(self.labels),'vertices':len(self.ages),'edges':len(self.edges),
                'reticulations':len(self.hybrids()),'level':level,
                'binary':True,'temporal_positive':True,'cut_child':True,
                'LSA_root':True,'all_vertices_outerplanar':outer}

    def local_mixture(self, selected: Iterable[str], t: int, mode: str) -> FrozenMixture:
        """Forward no-selected-merger law, exact at ages integer*log(2)."""
        selected=tuple(sorted(selected))
        if mode not in ('independent','common'): raise ValueError('Unknown inheritance rule')
        if any(x not in self.labels for x in selected): raise ValueError('Unknown selected taxon')
        if t<0: raise ValueError('Negative time')
        byid={e.id:e for e in self.edges}
        above='__ancestral_population__'
        rate={e.id:e.rate for e in self.edges};rate[above]=self.ancestral_rate
        state=tuple(self.incoming(x)[0].id for x in selected)
        dist={state:F(1)}
        now=0
        for age in sorted(a for a in set(self.ages.values()) if 0<a<=t):
            dt=age-now
            if dt:
                dist={s:w*F(1,2**sum(choose2(k)*rate[e]*dt for e,k in Counter(s).items()))
                      for s,w in dist.items()}
            for v in sorted(v for v in self.ages if self.ages[v]==age):
                outgoing={e.id for e in self.outgoing(v)}
                incoming=self.incoming(v)
                dd=defaultdict(F)
                for s,w in dist.items():
                    indices=[i for i,e in enumerate(s) if e in outgoing]
                    if not indices:
                        dd[s]+=w;continue
                    if len(incoming)<2:
                        dest=incoming[0].id if incoming else above
                        ss=list(s)
                        for i in indices:ss[i]=dest
                        dd[tuple(ss)]+=w
                    else:
                        g=self.inheritance[v]
                        assignments=[(c,)*len(indices) for c in (0,1)] if mode=='common' else product((0,1),repeat=len(indices))
                        for cs in assignments:
                            prob=(g if cs[0]==0 else 1-g) if mode=='common' else F(1)
                            ss=list(s)
                            for i,c in zip(indices,cs):
                                ss[i]=incoming[c].id
                                if mode=='independent':prob*=g if c==0 else 1-g
                            dd[tuple(ss)]+=w*prob
                dist=dict(dd)
            now=age
        if now<t:
            dist={s:w*F(1,2**sum(choose2(k)*rate[e]*(t-now) for e,k in Counter(s).items()))
                  for s,w in dist.items()}
        mass=sum(dist.values())
        components=[]
        for s,w in dist.items():
            blocks=defaultdict(list)
            for x,e in zip(selected,s):blocks[e].append(x)
            components.append((w/mass,tuple((tuple(b),rate[e]) for e,b in sorted(blocks.items()))))
        return FrozenMixture(selected,components)

    def switching_clusters(self):
        """Reference truth for one supplied fixture's finite switchings only."""
        hybrids=self.hybrids()
        allclusters={frozenset([x]) for x in self.labels}
        allclusters.add(frozenset(self.labels))
        trees=[]
        for cs in product((0,1),repeat=len(hybrids)):
            keep={self.incoming(h)[c].id for h,c in zip(hybrids,cs)}
            G=nx.DiGraph();G.add_nodes_from(self.ages)
            G.add_edges_from((e.parent,e.child) for e in self.edges
                            if e.child not in hybrids or e.id in keep)
            cl={}
            for v in reversed(list(nx.topological_sort(G))):
                cl[v]=frozenset([v]) if v in self.labels else frozenset().union(*(cl[w] for w in G.successors(v)))
            cc={c for c in cl.values() if c}
            allclusters |= cc
            trees.append(cc)
        return allclusters,trees


def make_source(name, ages, edgepairs, labels, gammas=None):
    edges=[Edge(f'e{i}',p,c,1+(i%3)) for i,(p,c) in enumerate(edgepairs)]
    src=Source(name,ages,tuple(sorted(labels)),edges,{},2)
    src.inheritance={h:F((gammas or {}).get(h,F(2,5))) for h in src.hybrids()}
    return src


def supplied_fixtures():
    fixtures=[]
    fixtures.append(make_source('balanced_tree',{'r':12,'u':2,'v':3,**dict.fromkeys('abcd',0)},
        [('r','u'),('r','v'),('u','a'),('u','b'),('v','c'),('v','d')],'abcd'))
    fixtures.append(make_source('one_hybrid_distinct_target',{'r':16,'B':12,'u':9,'v':8,'h':5,**dict.fromkeys('abcd',0)},
        [('r','B'),('r','d'),('B','u'),('B','v'),('u','a'),('u','h'),('v','b'),('v','h'),('h','c')],'abcd'))
    fixtures.append(make_source('independent_false_split_control',{'r':12,'u':9,'v':8,'h':5,'k':2,**dict.fromkeys('abcd',0)},
        [('r','u'),('r','v'),('u','c'),('u','h'),('v','d'),('v','h'),('h','k'),('k','a'),('k','b')],'abcd'))
    fixtures.append(make_source('root_containing_level2',{'r':12,'V':10,'U':8,'H1':5,'H2':4,'A':1,'B':2,**dict.fromkeys('abcd',0)},
        [('r','V'),('r','H1'),('V','U'),('V','H2'),('U','H1'),('U','H2'),('H1','A'),('H2','B'),('A','a'),('A','b'),('B','c'),('B','d')],'abcd'))
    fixtures.append(make_source('level2_variable_target',{'r':16,'R':12,'V':10,'U':8,'W':7,'H1':5,'H2':4,**dict.fromkeys('abcd',0)},
        [('r','R'),('r','d'),('R','V'),('R','W'),('V','U'),('V','H2'),('U','H1'),('U','H2'),('W','c'),('W','H1'),('H1','a'),('H2','b')],'abcd'))
    for L in (1,2,4,8):
        ages={'r':4*L+10,'A':1,'B':2,**dict.fromkeys('abcd',0)}
        ep=[('r','B'),('B','c'),('B','d'),('A','a'),('A','b')]
        child='A'
        for i in range(L):
            h=f'h{i}';u=f'u{i}'
            ages[h]=4*i+3;ages[u]=4*i+5
            ep.extend([(h,child),(u,h),(u,h)])
            child=u
        ep.append(('r',child))
        fixtures.append(make_source(f'serial_bigons_L{L}',ages,ep,'abcd'))
    # Replace the 'c' leaf in the first reticulation fixture by a positive cherry.
    base=fixtures[1]
    ages=dict(base.ages);ages['c']=2;ages['c1']=ages['c2']=0
    ep=[(e.parent,e.child) for e in base.edges]+[('c','c1'),('c','c2')]
    fixtures.append(make_source('hybrid_over_selected_cherry_5taxa',ages,ep,('a','b','c1','c2','d')))
    # Two independent blobs with disjoint descendant cherries and simultaneous events.
    ages={'r':30,**dict.fromkeys(('a','b','c','d','e','f'),0)}
    ep=[]
    for prefix,x,y,z in [('L','a','b','c'),('R','d','e','f')]:
        ages.update({prefix+'T':20,prefix+'U':16,prefix+'V':14,prefix+'H':8,prefix+'C':3})
        ep.extend([('r',prefix+'T'),(prefix+'T',prefix+'U'),(prefix+'T',prefix+'V'),
                   (prefix+'U',z),(prefix+'U',prefix+'H'),(prefix+'V',prefix+'H'),
                   (prefix+'V',prefix+'D'),(prefix+'H',prefix+'C'),
                   (prefix+'C',x),(prefix+'C',y)])
        # A new sampled leaf is needed on the other side to keep all binary degrees.
        ages[prefix+'D']=0
    labels=('a','b','c','d','e','f','LD','RD')
    fixtures.append(make_source('two_blobs_simultaneous_8taxa',ages,ep,labels))
    return fixtures
