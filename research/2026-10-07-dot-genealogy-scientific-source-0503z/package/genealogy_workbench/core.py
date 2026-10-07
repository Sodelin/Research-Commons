"""Exact, bounded source compiler. No unconstrained network recognition."""
from __future__ import annotations
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache
import json
from .vendor import forest_algebra as F

FAMILY = 'positive-independent-one-bigon-two-pad'
MAX_ROOTS = 5

class InputError(ValueError):
    pass

def rational(value, name='value'):
    if isinstance(value, bool) or not isinstance(value, (str, int, Q)):
        raise InputError(f'{name}: use an integer or exact rational string, never a JSON float')
    try:
        return Q(value)
    except (ValueError, ZeroDivisionError) as exc:
        raise InputError(f'{name}: invalid rational') from exc

def identifier(value, name):
    if not isinstance(value, str) or not value.strip() or len(value) > 256:
        raise InputError(f'{name}: expected a nonempty string of at most 256 characters')
    return value

def keys(data, allowed, required, name):
    if not isinstance(data, dict):
        raise InputError(f'{name}: expected an object')
    unknown = set(data) - set(allowed)
    missing = set(required) - set(data)
    if unknown or missing:
        raise InputError(f'{name}: unknown keys {sorted(unknown)}, missing keys {sorted(missing)}')

@dataclass(frozen=True)
class Source:
    source_id: str
    parameters: tuple[Q, Q, Q, Q, Q]  # leading, left, right, weight, trailing
    arm_ids: tuple[str, str]
    target_label: str | None = None

    @classmethod
    def read(cls, data):
        keys(data, ['source_id', 'family', 'parameters', 'arm_ids', 'target_label'],
             ['source_id', 'family', 'parameters', 'arm_ids'], 'source')
        if data['family'] != FAMILY:
            raise InputError(f'Unsupported source family: {data["family"]}')
        names = ['leading', 'left', 'right', 'weight', 'trailing']
        keys(data['parameters'], names, names, 'source parameters')
        p = tuple(rational(data['parameters'][n], n) for n in names)
        if not all(0 < v < 1 for v in p):
            raise InputError('This positive fixed-shape family requires all five parameters strictly between 0 and 1')
        arms = data['arm_ids']
        if not isinstance(arms, list) or len(arms) != 2:
            raise InputError('arm_ids: exactly two original arm IDs required')
        arms = tuple(identifier(v, 'arm ID') for v in arms)
        if arms[0] == arms[1]:
            raise InputError('Original arm IDs must be distinct')
        label = data.get('target_label')
        if label is not None:
            identifier(label, 'target_label')
        return cls(identifier(data['source_id'], 'source_id'), p, arms, label)

    def canonical_parameters(self):
        a,x,y,g,b = self.parameters
        bare = min((x,y,g), (y,x,1-g))
        return (a,*bare,b)

    def target(self, kind):
        if kind == 'trailing_survival':
            return {'trailing_survival': str(self.parameters[4])}
        if kind == 'canonical_source':
            return {'family': FAMILY, 'passive_arm_exchange_orbit': [str(v) for v in self.canonical_parameters()]}
        if kind == 'original_arm_assignment':
            a,x,y,g,b = self.parameters
            return {'leading': str(a), 'trailing': str(b), 'arms': sorted([
                {'arm_id': self.arm_ids[0], 'survival': str(x), 'weight': str(g)},
                {'arm_id': self.arm_ids[1], 'survival': str(y), 'weight': str(1-g)}], key=lambda r:r['arm_id'])}
        if kind == 'catalogue_label' and self.target_label is not None:
            return {'user_declared_catalogue_label': self.target_label}
        raise InputError(f'Unsupported or missing target: {kind}')

@dataclass(frozen=True)
class Experiment:
    experiment_id: str
    roots: tuple[tuple[str, str], ...]
    readout: str

    @classmethod
    def read(cls, data):
        keys(data, ['experiment_id', 'entering_roots', 'readout'], ['experiment_id', 'entering_roots', 'readout'], 'experiment')
        roots = data['entering_roots']
        if not isinstance(roots,list) or not 1 <= len(roots) <= MAX_ROOTS:
            raise InputError(f'entering_roots: runnable full-forest resource cap is 1..{MAX_ROOTS}; it is not a theorem cutoff')
        rows=[]
        for r in roots:
            keys(r,['copy_id','original_taxon_id'],['copy_id','original_taxon_id'],'entering root')
            rows.append((identifier(r['copy_id'],'copy_id'),identifier(r['original_taxon_id'],'original_taxon_id')))
        if len({r[0] for r in rows}) != len(rows):
            raise InputError('Duplicate original copy ID')
        if data['readout'] not in ('full_forest','root_count'):
            raise InputError('Only full_forest and root_count readouts are implemented')
        return cls(identifier(data['experiment_id'],'experiment_id'),tuple(rows),data['readout'])

    def encode(self, outcome):
        if self.readout == 'root_count':
            return self.decode(outcome)
        ids=[r[0] for r in self.roots]
        def enc(t):
            return ids[t] if isinstance(t,int) else [enc(t[0]),enc(t[1])]
        return [enc(t) for t in outcome]

    def decode(self, value):
        if self.readout == 'root_count':
            if isinstance(value,bool) or not isinstance(value,int) or not 1 <= value <= len(self.roots):
                raise InputError('Root-count outcome outside the declared experiment')
            return value
        if not isinstance(value,list) or not value:
            raise InputError('A full-forest outcome must be a nonempty list of rooted binary trees')
        lookup={r[0]:i for i,r in enumerate(self.roots)}; seen=[]
        def dec(t, depth=0):
            if depth > len(self.roots):
                raise InputError('Forest nesting exceeds the declared copy count')
            if isinstance(t,str) and t in lookup:
                seen.append(t); return lookup[t]
            if isinstance(t,list) and len(t)==2:
                return F.tree(dec(t[0],depth+1),dec(t[1],depth+1))
            raise InputError('Forest tree contains an unknown copy ID or is not rooted binary')
        f=F.forest(dec(t) for t in value)
        if sorted(seen) != sorted(lookup):
            raise InputError('Every declared original copy ID must appear exactly once in its forest outcome')
        return f

    def alphabet(self):
        return tuple(range(1,len(self.roots)+1)) if self.readout=='root_count' else F.forests(tuple(range(len(self.roots))))

@lru_cache(maxsize=256)
def complete_law(parameters, n):
    """E(a) B(x,y,g) E(b), retaining and grafting every built subtree."""
    a,x,y,g,b = parameters
    if not 1 <= n <= MAX_ROOTS:
        raise InputError('Unsupported root resource cap')
    dist=F.edge_law(n,a)
    for op in (lambda k:F.bigon_law(k,x,y,g,'independent'),lambda k:F.edge_law(k,b)):
        out=defaultdict(Q)
        for forest,p in dist.items():
            for tokens,q in op(len(forest)).items():
                out[F.graft(forest,tokens)] += p*q
        dist=dict(out)
    if sum(dist.values(),Q(0)) != 1 or any(p<0 for p in dist.values()):
        raise ArithmeticError('Exact full-forest kernel failed normalization')
    return dist

def law(source,experiment):
    d=complete_law(source.parameters,len(experiment.roots))
    if experiment.readout=='full_forest':
        return d
    out=defaultdict(Q)
    for f,p in d.items():out[len(f)]+=p
    return dict(out)

def law_entries(source,experiment):
    return [{'outcome':experiment.encode(f) if experiment.readout=='full_forest' else f,'probability':str(law(source,experiment).get(f,Q(0)))} for f in experiment.alphabet()]

def equivalence(left,right):
    """Accepted theorem-derived relation; not an executed QE/cutoff search."""
    same=left.canonical_parameters()==right.canonical_parameters()
    a,x,y,g,b=left.parameters; aa,xx,yy,gg,bb=right.parameters
    branches=[]
    if (a,b)==(aa,bb) and (x,y,g)==(xx,yy,gg):branches.append('same_parameters')
    if (a,b)==(aa,bb) and (x,y,g)==(yy,xx,1-gg):branches.append('arm_exchange')
    return {'equivalent':same,'branches':branches,'evidence_tier':'theorem_derived_fixed_shape',
        'contract':'All finite complete forest kernels of the strictly positive independent one-bigon/two-pad family; passive private current-root routing',
        'theorem_reference':'G4-UNKNOWN-BARE-ONE-BIGON-REVIEW@f43d0f2da6ad112fe62a98abc47deb74d9d59973',
        'implemented_arithmetic':'exact rational parameter comparison','finite_determining_cutoff_executed':False,'lean_kernel_checked':False,
        'limits':['No equality against arbitrary unknown-size sources','No actuator/original-arm equivalence claim','No noisy-law identification claim']}

def read_job(job):
    keys(job,['schema','catalogue','experiments','target','exact_observations','sampling','records'],['schema','catalogue','experiments','target'],'job')
    if job['schema']!='genealogy-workbench/job-v1':raise InputError('Unsupported job schema')
    cat=job['catalogue']
    keys(cat,['catalogue_id','coverage','sources'],['catalogue_id','coverage','sources'],'catalogue')
    identifier(cat['catalogue_id'],'catalogue_id')
    if cat['coverage']!='only_listed_sources':raise InputError('Catalogue coverage must explicitly be only_listed_sources')
    if not isinstance(cat['sources'],list) or not 1 <= len(cat['sources']) <= 128:raise InputError('Expected 1..128 supplied sources')
    sources=tuple(Source.read(d) for d in cat['sources'])
    if len({s.source_id for s in sources})!=len(sources):raise InputError('Duplicate source ID')
    if not isinstance(job['experiments'],list) or not 1 <= len(job['experiments']) <= 32:raise InputError('Expected 1..32 predeclared experiment rows')
    experiments=tuple(Experiment.read(d) for d in job['experiments'])
    if len({e.experiment_id for e in experiments})!=len(experiments):raise InputError('Duplicate experiment ID')
    keys(job['target'],['kind'],['kind'],'target')
    kind=job['target']['kind']
    for s in sources:s.target(kind)
    return sources,experiments,kind

def target_result(sources,kind):
    answers={json.dumps(s.target(kind),sort_keys=True,separators=(',',':')) for s in sources}
    return {'status':'INCOMPATIBLE' if not sources else 'CERTIFIED_WITHIN_CATALOGUE' if len(answers)==1 else 'ABSTAIN_AMBIGUOUS',
        'compatible_source_ids':[s.source_id for s in sources], 'target_answers':[json.loads(v) for v in sorted(answers)],
        'answer':json.loads(next(iter(answers))) if len(answers)==1 else None,
        'coverage':'within the declared finite catalogue only; arbitrary hidden sources are not covered'}

def exact_sort(job):
    if 'records' in job or 'sampling' in job:
        raise InputError('Exact-law sorting cannot silently accept empirical locus records or sampling assumptions')
    sources,experiments,kind=read_job(job);exps={e.experiment_id:e for e in experiments}
    rows=job.get('exact_observations')
    if not isinstance(rows,list) or not rows:raise InputError('At least one exact-law observation row is required')
    seen=set(); laws={}; explanations=[]
    for row in rows:
        keys(row,['experiment_id','probabilities'],['experiment_id','probabilities'],'exact observation')
        eid=identifier(row['experiment_id'],'observed experiment_id')
        if eid not in exps or eid in seen:raise InputError('Unknown or duplicate exact observation experiment ID')
        seen.add(eid);exp=exps[eid]; dist={}
        if not isinstance(row['probabilities'],list):raise InputError('probabilities must be a list')
        for v in row['probabilities']:
            keys(v,['outcome','probability'],['outcome','probability'],'probability entry')
            outcome=exp.decode(v['outcome']);p=rational(v['probability'],'probability')
            if p<0 or p>1 or outcome in dist:raise InputError('Duplicate outcome or invalid probability')
            dist[outcome]=p
        if sum(dist.values(),Q(0))!=1:raise InputError('Exact observed law must sum to one; absent coordinates mean zero')
        laws[eid]=dist
    compatible=[]
    for s in sources:
        mismatch=None
        for eid,observed in laws.items():
            expected=law(s,exps[eid])
            for out in exps[eid].alphabet():
                if expected.get(out,Q(0))!=observed.get(out,Q(0)):
                    mismatch={'experiment_id':eid,'outcome':exps[eid].encode(out) if exps[eid].readout=='full_forest' else out,
                        'observed':str(observed.get(out,Q(0))),'expected':str(expected.get(out,Q(0)))};break
            if mismatch:break
        if mismatch:explanations.append({'source_id':s.source_id,'first_exact_mismatch':mismatch})
        else:compatible.append(s)
    result=target_result(compatible,kind)
    result.update(evidence_tier='exact_finite_catalogue',catalogue_id=job['catalogue']['catalogue_id'],
        observation='exact full probability laws, never empirical estimates',target_kind=kind,eliminated_sources=explanations,
        observed_experiment_ids=list(laws),shared_source_parameters_across_rows=True,lean_kernel_checked=False,
        original_copy_and_taxon_ids={e.experiment_id:[{'copy_id':c,'original_taxon_id':t} for c,t in e.roots] for e in experiments})
    return result
