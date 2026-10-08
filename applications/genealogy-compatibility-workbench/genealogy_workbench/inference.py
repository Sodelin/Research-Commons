"""One accepted exact-law inference branch; source membership is a promise."""
from fractions import Fraction as Q
from .core import FAMILY,Experiment,InputError,keys,rational
from .vendor import forest_algebra as F


def recover_trailing_four(data):
    keys(data,['source_family_promise','experiment','probabilities'],['source_family_promise','experiment','probabilities'],'trailing-pad input')
    if data['source_family_promise']!=FAMILY:raise InputError('Unsupported or missing positive one-bigon/two-pad source promise')
    e=Experiment.read(data['experiment'])
    if len(e.roots)!=4 or e.readout!='full_forest':raise InputError('This branch requires the complete exact four-root labelled forest law')
    dist={}
    if not isinstance(data['probabilities'],list):raise InputError('probabilities must be a list')
    for v in data['probabilities']:
        keys(v,['outcome','probability'],['outcome','probability'],'probability entry')
        f=e.decode(v['outcome']);p=rational(v['probability'],'probability')
        if f in dist or not 0<=p<=1:raise InputError('Duplicate forest coordinate or invalid probability')
        dist[f]=p
    if sum(dist.values(),Q(0))!=1:raise InputError('Exact observed law must sum to one')
    p1=sum((p for f,p in dist.items() if len(f)==1),Q(0));p2=sum((p for f,p in dist.items() if len(f)==2),Q(0))
    two_cherries=sum((p for f,p in dist.items() if len(f)==2 and all(len(F.leaves(t))==2 for t in f)),Q(0))
    balanced=sum((p for f,p in dist.items() if len(f)==1 and all(len(F.leaves(t))==2 for t in f[0])),Q(0))
    c=two_cherries-p2/3;h=balanced-p1/3
    base={'evidence_tier':'theorem_derived_exact_law_conditional_on_source_promise','source_family_promise':FAMILY,
        'source_membership_verified':False,'full_forest_four_root_coordinates_used':True,'C':str(c),'H':str(h),
        'identity':'C(K)=a^6 b C(B); H(K)=a^6(1-b) C(B)',
        'theorem_reference':'G4-UNKNOWN-BARE-ONE-BIGON-REVIEW@f43d0f2da6ad112fe62a98abc47deb74d9d59973',
        'lean_kernel_checked':False,'whole_five_parameter_recovery':False,
        'original_copy_and_taxon_ids':[{'copy_id':v,'original_taxon_id':t} for v,t in e.roots]}
    if c+h==0:
        if c or h:
            return {**base,'status':'ABSTAIN_SOURCE_PROMISE_CONFLICT','answer':None,
                'reason':'The zero denominator has nonzero C/H, contradicting the promised positive source identities'}
        return {**base,'status':'ABSTAIN_DEGENERATE_BRANCH','answer':None,
            'reason':'The four-root denominator vanishes. Accepted five/six-root spectral branches are not implemented here; this does not prove non-identifiability'}
    b=c/(c+h)
    if not 0<b<1:
        return {**base,'status':'ABSTAIN_SOURCE_PROMISE_CONFLICT','answer':None,'reason':'The implied trailing survival violates the strictly positive source promise'}
    return {**base,'status':'CONDITIONAL_EXACT_LAW_INFERENCE','answer':{'trailing_survival':str(b)},
        'scope':'Trailing survival only, conditional on the supplied source-family promise and an exact complete law; no recognition of arbitrary input networks'}
