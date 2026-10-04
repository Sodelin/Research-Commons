#!/usr/bin/env python3
"""Independent rational replay of the supplied COMMON impossibility witness.

The source-level conditional probability rule is an explicit mathematical
contract. This checker does not infer scientific admission of supplied laws.
"""
from fractions import Fraction as Q
import json
import hashlib
from pathlib import Path
import argparse

def verify(request,certificate):
    fields={'schema','observation_kind','source_contract','protected_site','mechanisms','taxa','profiles'}
    if not isinstance(request,dict) or set(request)!=fields or request['schema']!='unknown-size-common-intervention-profile-v1':raise ValueError('Unadmitted request fields/schema.')
    if request['observation_kind']!='exact_unranked_law' or request['source_contract']!='positive-rooted-LSA-outer-labelled-planar-cut-child-common-product-register-v1':raise ValueError('Wrong exact-source contract.')
    if certificate['source_contract']!=request['source_contract'] or certificate['protected_original_site']!=request['protected_site']:raise ValueError('Original source/site binding changed.')
    if 'common' not in request['mechanisms']:raise ValueError('COMMON hypothesis not present.')
    modes=request['mechanisms']
    if not isinstance(modes,list) or not modes or len(set(modes))!=len(modes) or set(modes)-{'common','independent'}:raise ValueError('Invalid source mechanism carrier.')
    if not isinstance(request['protected_site'],str) or not request['protected_site']:raise ValueError('Invalid protected original site.')
    if hashlib.sha256(json.dumps(request,sort_keys=True,separators=(',',':')).encode()).hexdigest()!=certificate['request_sha256']:raise ValueError('Exact request binding changed.')
    taxa=request['taxa']
    if not isinstance(taxa,list) or len(taxa)<2 or len(set(taxa))!=len(taxa) or any(not isinstance(t,str) or not t for t in taxa):raise ValueError('Invalid original taxon carrier.')
    if not isinstance(request['profiles'],list) or not request['profiles']:raise ValueError('Empty/malformed profile carrier.')
    seen=set()
    left=[];right=[];names=[]
    for profile in request['profiles']:
        if not isinstance(profile,dict) or set(profile)!={'id','sample_panel','coordinate_ids','background_controls','laws'}:raise ValueError('Invalid profile fields.')
        if not isinstance(profile['id'],str) or profile['id'] in seen:raise ValueError('Duplicate/invalid profile name.')
        seen.add(profile['id']);panel=profile['sample_panel'];labels=[]
        if not isinstance(panel,dict) or set(panel)-set(taxa):raise ValueError('Mismatched original sample taxa.')
        for copies in panel.values():
            if not isinstance(copies,list) or not copies or any(not isinstance(v,str) or not v for v in copies):raise ValueError('Invalid fixed copy panel.')
            labels.extend(copies)
        if not labels or len(set(labels))!=len(labels):raise ValueError('Copy labels not unique/nonempty.')
        background=profile['background_controls']
        if not isinstance(background,dict) or request['protected_site'] in background or any(not isinstance(k,str) or type(v) is not int or v not in (0,1) for k,v in background.items()):raise ValueError('Mismatched background controls.')
        order=profile['coordinate_ids']
        if not isinstance(order,list) or not order or len(set(order))!=len(order) or any(not isinstance(v,str) for v in order):raise ValueError('Invalid shared coordinate frame.')
        if set(profile['laws'])!={'natural','force0','force1'}:raise ValueError('Wrong intervention triple.')
        n=len(profile['coordinate_ids']);v={}
        for tag,data in profile['laws'].items():
            if not isinstance(data,list) or len(data)!=n or any(type(x) is not int and not isinstance(x,str) for x in data):raise ValueError('Wrong rational coordinate shape.')
            values=list(map(Q,data))
            if sum(values)!=1 or min(values)<0:raise ValueError('Invalid probability vector.')
            v[tag]=values
        for k,key in enumerate(profile['coordinate_ids']):
            names.append([profile['id'],key]);left.append(v['natural'][k]-v['force1'][k]);right.append(v['force0'][k]-v['force1'][k])
    if names!=certificate['coordinate_order']:raise ValueError('Coordinate labels/order changed.')
    proof=certificate['proof'];kind=proof['kind']
    if kind=='NONZERO_SHARED_PARAMETER_MINOR':
        i,j=proof['coordinates']
        if any(type(k) is not int or not 0<=k<len(names) for k in (i,j)):raise ValueError('Invalid minor indices.')
        value=left[i]*right[j]-left[j]*right[i]
        if not value or value!=Q(proof['minor_value']):raise ValueError('Nonzero rational minor did not replay.')
    elif kind=='FORCED_ROWS_EQUAL_NATURAL_DIFFERS':
        i=proof['coordinate']
        if any(right) or not left[i] or left[i]!=Q(proof['nonzero_difference']):raise ValueError('Equal-row contradiction did not replay.')
    elif kind=='COMMON_INTERIOR_PARAMETER_VIOLATION':
        i=proof['coordinate']
        if not right[i]:raise ValueError('No forced gamma ratio.')
        gamma=left[i]/right[i]
        if gamma!=Q(proof['forced_gamma']) or 0<gamma<1:raise ValueError('Interior violation did not replay.')
    else:raise ValueError('Unknown impossibility proof kind.')
    expected='GLOBAL_UNKNOWN_SIZE_UNSAT_FOR_DECLARED_COMMON_MODEL' if request['mechanisms']==['common'] else 'UNKNOWN_UNION_COMMON_COMPONENT_EXCLUDED_INDEPENDENT_UNCHECKED'
    if certificate['status']!=expected or certificate['graph_size_bound_used'] is not False or certificate['catalogue_enumeration_used'] is not False:raise ValueError('Unsupported global/union claim.')
    return {'status':'PASS_INDEPENDENT_EXACT_COMMON_IMPOSSIBILITY_REPLAY','hypothesis':'declared original COMMON product-register model only','unknown_hidden_size_covered':True,'empirical_admission_claimed':False}

def main():
    p=argparse.ArgumentParser();p.add_argument('request');p.add_argument('certificate');a=p.parse_args();print(json.dumps(verify(json.loads(Path(a.request).read_bytes()),json.loads(Path(a.certificate).read_bytes())),indent=2))

if __name__=='__main__':main()
