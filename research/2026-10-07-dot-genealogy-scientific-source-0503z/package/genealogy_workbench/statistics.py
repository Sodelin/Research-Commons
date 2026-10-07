"""All-time fresh-locus catalogue filtering with exact conservative radii."""
from collections import Counter
from fractions import Fraction as Q
from math import isqrt
from .core import InputError, identifier, keys, rational, read_job, law, target_result


def ceil_log2(q):
    n=0;power=Q(1)
    while power<q:n+=1;power*=2
    return n

def sqrt_upper(q,scale=10**9):
    scaled=q*scale*scale
    root=isqrt(scaled.numerator//scaled.denominator)
    if root*root*scaled.denominator<scaled.numerator:root+=1
    return Q(root,scale)

def radius(n,d,alpha_row):
    if n<1 or d<1 or not 0<alpha_row<1:raise InputError('Invalid confidence radius arguments')
    # ln(R) <= ceil(log2 R), since ln 2 < 1. Every operation here is exact.
    R=Q(2*d*n*(n+1))/alpha_row
    return min(Q(1),sqrt_upper(Q(ceil_log2(R),2*n)))

def statistical_sort(job):
    if 'exact_observations' in job:
        raise InputError('Fresh-locus sorting cannot silently mix exact-law observations with empirical counts')
    sources,experiments,kind=read_job(job);exps={e.experiment_id:e for e in experiments}
    sampling=job.get('sampling')
    keys(sampling,['unit','independent_fresh_loci','fixed_row_laws','row_selected_before_outcome','channel','alpha','eta'],
        ['unit','independent_fresh_loci','fixed_row_laws','row_selected_before_outcome','channel','alpha','eta'],'sampling')
    if sampling['unit']!='one_joint_outcome_per_locus':raise InputError('One joint outcome per locus is required')
    if not all(sampling[k] is True for k in ['independent_fresh_loci','fixed_row_laws','row_selected_before_outcome']):
        raise InputError('The conditional statistical contract requires fresh independent loci, fixed iid row laws and selection before observing the outcome')
    if sampling['channel']!='declared_interface_readout':
        raise InputError('Uncalibrated DNA/estimated tree channels cannot be promoted to interface forest laws')
    alpha=rational(sampling['alpha'],'alpha');eta=rational(sampling['eta'],'eta')
    if not 0<alpha<1 or not 0<=eta<=1:raise InputError('Require 0<alpha<1 and 0<=eta<=1')
    records=job.get('records')
    if not isinstance(records,list) or not records or len(records)>1000000:raise InputError('Expected 1..1000000 locus records')
    counts={e.experiment_id:Counter() for e in experiments};ns=Counter();seen={};ignored=0
    candidates={s.source_id:s for s in sources}; eliminated=[];history=[]
    expected={s.source_id:{eid:law(s,e) for eid,e in exps.items()} for s in sources}
    ar=alpha/len(experiments)
    for rec in records:
        keys(rec,['locus_id','experiment_id','outcome'],['locus_id','experiment_id','outcome'],'locus record')
        lid=identifier(rec['locus_id'],'locus_id');eid=identifier(rec['experiment_id'],'experiment_id')
        if eid not in exps:raise InputError('Unknown experiment ID in locus record')
        out=exps[eid].decode(rec['outcome'])
        if lid in seen:
            if seen[lid]!=(eid,out):raise InputError('Different records for the same locus require an actual joint-outcome compiler; refusing pseudoreplication')
            ignored+=1;continue
        seen[lid]=(eid,out);ns[eid]+=1;counts[eid][out]+=1;n=ns[eid]
        b=radius(n,len(exps[eid].alphabet()),ar)
        for sid in list(candidates):
            bad=next((v for v in exps[eid].alphabet() if abs(Q(counts[eid][v],n)-expected[sid][eid].get(v,Q(0)))>b+eta),None)
            if bad is not None:
                eliminated.append({'source_id':sid,'experiment_id':eid,'row_prefix_loci':n,'outcome':exps[eid].encode(bad) if exps[eid].readout=='full_forest' else bad,
                    'empirical':str(Q(counts[eid][bad],n)),'candidate':str(expected[sid][eid].get(bad,Q(0))),
                    'radius_upper':str(b),'eta':str(eta)})
                del candidates[sid]
                history.append({'unique_loci':len(seen),'remaining_source_ids':list(candidates)})
    result=target_result(list(candidates.values()),kind)
    if result['status']=='CERTIFIED_WITHIN_CATALOGUE':result['status']='CONDITIONAL_CERTIFICATE_WITHIN_CATALOGUE'
    if result['status']=='INCOMPATIBLE':result['status']='ABSTAIN_MODEL_OR_CONFIDENCE_CONFLICT'
    result.update(evidence_tier='conditional_statistical_finite_catalogue',catalogue_id=job['catalogue']['catalogue_id'],target_kind=kind,
        alpha=str(alpha),eta=str(eta),confidence_scope='One simultaneous event of probability at least 1-alpha over every sample count of each predeclared experiment row; conditional on the stated sampling and channel assumptions and truth lying in the listed catalogue',
        independent_observation_units=len(seen),identical_same_locus_duplicates_ignored=ignored,
        row_counts=dict(ns),row_final_radii={eid:str(radius(n,len(exps[eid].alphabet()),ar)) for eid,n in ns.items()},
        eliminated_sources=eliminated,compatibility_shrinkage=history,intersects_all_observed_prefix_constraints=True,
        radius_method='Exact rational upper bound sqrt(ceil(log2(2 D k(k+1)/alpha_row))/(2k)); sqrt rounded upward to 1e-9; Hoeffding plus coordinate/row/time union bounds',
        assumptions_verified_by_program=False,computational_error='0 (exact finite candidate laws)',source_image_coverage='only the supplied finite points; no continuous closure/net claim',
        channel_calibration='eta is user-declared, not estimated or validated here',lean_kernel_checked=False,
        original_copy_and_taxon_ids={e.experiment_id:[{'copy_id':c,'original_taxon_id':t} for c,t in e.roots] for e in experiments})
    return result
