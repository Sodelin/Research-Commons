"""Exact complete-panel extraction and conditional confidence composition.

Trusted registry identities come from independent admission review, never from a
PASS field in the dataset. Protocol records cannot issue data-confidence claims.
"""
import hashlib,json,re,sys
from fractions import Fraction as F
from pathlib import Path
BASE=Path(__file__).resolve().parent
PROVIDER=BASE.parent/'msci-ab-profile-implementation-20261005-1612z'
PROVIDER_MANIFEST_SHA='f156c3f82fee8a85bafe6671adb4ed00e6661695018db1e295b28ffeeae87e4e'
MAX_BYTES=16*1024**2;MAX_LOCI=100000;MAX_ID=64
TRUSTED_REGISTRY_SHA='bb75317a350a2d8d24d629154da48cc6d04796dc7e2a8c787fc71a39cf1de860'
LABELS=('A1','A2','B1','B2','C1','C2')
FEATURES=('AC1','AC2','CC1','BC1','BC2','AB1','AB2','AA1','BB1')
PAIRS={'AA':('A1','A2'),'BB':('B1','B2'),'CC':('C1','C2'),'AB':('A1','B1'),'BC':('B1','C1'),'AC':('A1','C1')}
CHI={'A':1,'C':1,'G':-1,'T':-1}
MODEL='fixed-six-copy-clock-jc-nine-v1'
class EvidenceInvalid(ValueError):pass
class NotAdmitted(ValueError):pass
class InputResource(ValueError):pass

def sha(raw):return hashlib.sha256(raw).hexdigest()
def canonical(value):return (json.dumps(value,sort_keys=True,separators=(',',':'))+'\n').encode()
def no_duplicates(pairs):
    out={}
    for k,v in pairs:
        if k in out:raise EvidenceInvalid('duplicate JSON key')
        out[k]=v
    return out

def read(path,expected):
    if not isinstance(expected,str) or not re.fullmatch('[0-9a-f]{64}',expected):raise EvidenceInvalid('external digest required')
    p=Path(path)
    if p.is_symlink():raise EvidenceInvalid('symlink input')
    if p.stat().st_size>MAX_BYTES:raise InputResource('file byte cap')
    raw=p.read_bytes()
    if len(raw)>MAX_BYTES:raise InputResource('file byte cap')
    if sha(raw)!=expected:raise EvidenceInvalid('file identity mismatch')
    def reject(_):raise EvidenceInvalid('noninteger JSON number')
    return json.loads(raw,object_pairs_hook=no_duplicates,parse_float=reject,parse_constant=reject)

def rational(value):
    if not isinstance(value,str) or len(value)>160 or not re.fullmatch('-?[0-9]+(?:/[0-9]+)?',value):raise EvidenceInvalid('rational encoding')
    try:q=F(value)
    except (ValueError,ZeroDivisionError) as error:raise EvidenceInvalid('rational syntax') from error
    if max(abs(q.numerator).bit_length(),q.denominator.bit_length())>256:raise InputResource('reduced rational cap')
    return q

def exact_keys(obj,keys,label):
    if not isinstance(obj,dict) or set(obj)!=set(keys):raise EvidenceInvalid(label+' schema')

def load_provider():
    pins=read(PROVIDER/'SOURCE-PINS.json',PROVIDER_MANIFEST_SHA)
    expected={'interval_math.py','base_contractors.py','interval_ad.py','joint_contractor.py','global_contractors.py','global_engine.py','global_check.py','bounded_runner.py','prepare_controls.py'}
    if set(pins)!=expected:raise EvidenceInvalid('provider source allowlist')
    for name,digest in pins.items():
        p=PROVIDER/name
        if p.is_symlink() or sha(p.read_bytes())!=digest:raise EvidenceInvalid('provider source changed')
        loaded=sys.modules.get(p.stem)
        if loaded is not None and Path(loaded.__file__).resolve()!=p.resolve():raise EvidenceInvalid('conflicting imported provider')
    sys.path.insert(0,str(PROVIDER))
    import global_engine
    return global_engine

def request(path,expected):
    d=read(path,expected)
    exact_keys(d,('schema','dataset_sha256','admission_sha256','delta','domain','normalized_width_targets','inverse_budget','radius_steps','expected_loci','selection_sha256','provenance'),'analysis request')
    if d['schema']!='phased-nine-feature-analysis-v1':raise EvidenceInvalid('analysis schema')
    delta=rational(d['delta'])
    if not 0<delta<1:raise EvidenceInvalid('delta outside (0,1)')
    if type(d['expected_loci']) is not int or not 1<=d['expected_loci']<=MAX_LOCI:raise InputResource('locus count cap')
    if type(d['radius_steps']) is not int or not 0<=d['radius_steps']<=24:raise InputResource('radius search cap')
    for key in ('dataset_sha256','admission_sha256','selection_sha256'):
        if not isinstance(d[key],str) or not re.fullmatch('[0-9a-f]{64}',d[key]):raise EvidenceInvalid('request digest')
    if not isinstance(d['provenance'],dict):raise EvidenceInvalid('provenance mapping')
    return d,delta

def premise_identity(req):
    return sha(canonical({key:req[key] for key in ('dataset_sha256','selection_sha256','expected_loci','delta','domain','normalized_width_targets','inverse_budget','radius_steps')}))

def admission(path,registry_path,registry_sha,req):
    if registry_sha!=TRUSTED_REGISTRY_SHA:raise NotAdmitted('registry identity is not anchored in reviewed source')
    registry=read(registry_path,registry_sha);exact_keys(registry,('schema','admissions'),'reviewed registry')
    if registry['schema']!='externally-reviewed-admission-registry-v1' or not isinstance(registry['admissions'],dict):raise NotAdmitted('unsupported registry')
    if len(registry['admissions'])>128:raise InputResource('admission registry count cap')
    entry=registry['admissions'].get(req['admission_sha256'])
    if not isinstance(entry,dict):raise NotAdmitted('admission absent from trusted registry')
    exact_keys(entry,('classification','review_scope'),'registry entry')
    classification=entry['classification']
    if classification not in ('protocol_fixture','scientifically_admitted'):raise NotAdmitted('unsupported admission class')
    a=read(path,req['admission_sha256']);exact_keys(a,('schema','model','dataset_sha256','analysis_premises_sha256','selection_sha256','locus_count','classification','premises','review_notes'),'admission')
    if type(a['locus_count']) is not int or not isinstance(a['review_notes'],str) or len(a['review_notes'])>4096:raise EvidenceInvalid('admission metadata types')
    if a['schema']!='reviewed-phased-design-v1' or a['model']!=MODEL or a['classification']!=classification:raise NotAdmitted('admission channel/class mismatch')
    if a['dataset_sha256']!=req['dataset_sha256'] or a['analysis_premises_sha256']!=premise_identity(req) or a['selection_sha256']!=req['selection_sha256'] or a['locus_count']!=req['expected_loci']:raise NotAdmitted('admission does not bind this fixed analysis/design')
    exact_keys(a['premises'],('A1','A2','A3','A4','A5','A6'),'scientific premises')
    required='assumed_under_independent_scientific_review' if classification=='scientifically_admitted' else 'not_asserted_protocol_fixture'
    if any(v!=required for v in a['premises'].values()):raise NotAdmitted('scientific premises unsupported')
    if entry['review_scope']!=('scientific_and_design' if classification=='scientifically_admitted' else 'protocol_semantics_only'):raise NotAdmitted('registry review scope')
    return a

def extract(data,expected_loci,selection_sha):
    if type(expected_loci) is not int or not 1<=expected_loci<=MAX_LOCI:raise InputResource('locus count cap')
    exact_keys(data,('schema','loci'),'dataset')
    if data['schema']!='complete-six-copy-two-site-loci-v1' or not isinstance(data['loci'],list):raise EvidenceInvalid('dataset schema')
    if len(data['loci'])!=expected_loci:raise EvidenceInvalid('incomplete or excess locus stream')
    counts={name:0 for name in FEATURES};seen=set();selection=[]
    for locus in data['loci']:
        exact_keys(locus,('id','columns','calls'),'locus')
        name=locus['id']
        if not isinstance(name,str) or not re.fullmatch('[A-Za-z0-9_-]{1,64}',name) or name in seen:raise EvidenceInvalid('invalid or duplicate locus identity')
        seen.add(name);columns=locus['columns']
        if not isinstance(columns,list) or len(columns)!=2 or any(type(x) is not int or not 1<=x<=1000000000 for x in columns) or columns[0]>=columns[1]:raise EvidenceInvalid('two preselected ordered columns required')
        exact_keys(locus['calls'],LABELS,'six-copy panel')
        if any(not isinstance(value,str) or not re.fullmatch('[ACGT]{2}',value) for value in locus['calls'].values()):raise EvidenceInvalid('complete phased uppercase calls required')
        selection.append({'id':name,'columns':columns})
        for feature in FEATURES:
            x,y=PAIRS[feature[:2]];parity=1
            for site in range(int(feature[-1])):parity*=CHI[locus['calls'][x][site]]*CHI[locus['calls'][y][site]]
            counts[feature]+=(1+parity)//2
    if sha(canonical(selection))!=selection_sha:raise EvidenceInvalid('column selection provenance mismatch')
    return {'schema':'literal-nine-feature-counts-v1','m':expected_loci,'counts':counts,'feature_order':list(FEATURES),'character':CHI,'pairs':{k:list(v) for k,v in PAIRS.items()},'selection_sha256':selection_sha,'complete_extraction':True,'within_locus_feature_independence_assumed':False}

def confidence(extraction,delta,steps,exp_neg=None):
    if extraction.get('complete_extraction') is not True or extraction.get('feature_order')!=list(FEATURES):raise EvidenceInvalid('complete extraction receipt required')
    m=extraction['m'];counts=extraction['counts']
    if type(m) is not int or not 1<=m<=MAX_LOCI or set(counts)!=set(FEATURES) or any(type(k) is not int or not 0<=k<=m for k in counts.values()):raise EvidenceInvalid('count bounds')
    if not isinstance(delta,F) or not 0<delta<1 or type(steps) is not int or not 0<=steps<=24:raise EvidenceInvalid('confidence parameters')
    if exp_neg is None:exp_neg=load_provider().m.forward.exp_neg
    lo=F(0);hi=F(1);candidate=None;log=[];refusal=None
    for _ in range(steps):
        r=(lo+hi)/2;x=2*m*r*r
        try:bound=exp_neg(x,80)
        except (ValueError,ArithmeticError) as error:refusal=type(error).__name__;break
        if not 0<=bound.lo<=bound.hi<=1:raise EvidenceInvalid('invalid exponential enclosure')
        passed=18*bound.hi<=delta;log.append({'radius':str(r),'exponent':str(x),'exp_interval':[str(bound.lo),str(bound.hi)],'union_error_upper':str(18*bound.hi),'certified':passed})
        if passed:candidate=(r,bound);hi=r
        else:lo=r
    if candidate is None:r=F(1);mode='FULL_RANGE_CERTIFIED';error=F(0)
    else:r,bound=candidate;mode='HOEFFDING_UNION_BOUND_CERTIFIED';error=18*bound.hi
    box={key:[str(max(F(0),F(counts[key],m)-r)),str(min(F(1),F(counts[key],m)+r))] for key in FEATURES}
    raw={}
    for key,(lower,upper) in box.items():
        a=max(F(0),2*F(lower)-1);b=min(F(1),2*F(upper)-1);raw[key]={'lower':str(a),'upper':str(b),'empty':a>b}
    return {'schema':'simultaneous-nine-feature-box-v1','mode':mode,'delta':str(delta),'m':m,'radius':str(r),'error_upper_bound':str(error),'shifted_mean_box':box,'raw_moment_projection':raw,'union_factor':18,'within_locus_feature_independence_assumed':False,'radius_depends_on_counts':False,'search_steps_limit':steps,'arithmetic_bits':80,'search':log,'arithmetic_refusal':refusal,'biological_coverage_claimed_by_arithmetic_alone':False}

def inverse_request(req,box,analysis_sha,counts_sha,confidence_sha):
    return {'schema':'global-triangular-request-v1','model':MODEL,'quantity':'shifted_bernoulli_character_mean','box':req['domain'],'features':box['shifted_mean_box'],'normalized_width_targets':req['normalized_width_targets'],'budget':req['inverse_budget'],'provenance':{'kind':'phased_count_confidence_composition','analysis_request_sha256':analysis_sha,'dataset_sha256':req['dataset_sha256'],'admission_sha256':req['admission_sha256'],'extraction_sha256':counts_sha,'confidence_sha256':confidence_sha,'delta':req['delta'],'scientific_premises_are_external':True}}
