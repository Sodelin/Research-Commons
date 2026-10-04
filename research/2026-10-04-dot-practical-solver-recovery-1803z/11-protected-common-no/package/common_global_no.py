#!/usr/bin/env python3
"""Exact all-size necessary condition at ONE protected COMMON source site.

No graph census or word bound is used. A failure excludes the declared COMMON
model for every finite hidden size. Passing is UNKNOWN, never source SAT.
"""
import argparse
from fractions import Fraction as F
import json
import hashlib
from pathlib import Path

CONTRACT='positive-rooted-LSA-outer-labelled-planar-cut-child-common-product-register-v1'

def admitted(request):
    if not isinstance(request,dict) or set(request)!={'schema','observation_kind','source_contract','protected_site','mechanisms','taxa','profiles'}:
        raise ValueError('Unsupported request shape; no empirical/data adapter is provided.')
    if request['schema']!='unknown-size-common-intervention-profile-v1' or request['observation_kind']!='exact_unranked_law':
        raise ValueError('Declared exact unranked-law profile required, not DNA/frequencies.')
    if request['source_contract']!=CONTRACT or not isinstance(request['protected_site'],str) or not request['protected_site']:
        raise ValueError('Exact original-source/common product-register contract and marked original site required.')
    mechanisms=request['mechanisms']
    if not isinstance(mechanisms,list) or not mechanisms or len(set(mechanisms))!=len(mechanisms) or set(mechanisms)-{'common','independent'}:
        raise ValueError('Mechanism hypotheses must be an explicit nonempty common/independent list.')
    taxa=request['taxa']
    if not isinstance(taxa,list) or len(taxa)<2 or len(set(taxa))!=len(taxa) or any(not isinstance(v,str) or not v for v in taxa):
        raise ValueError('A fixed finite original taxon carrier is required.')
    if not isinstance(request['profiles'],list) or not request['profiles']:raise ValueError('At least one matched intervention triple required.')
    identifiers=set();a=[];b=[];coordinates=[]
    for group in request['profiles']:
        if not isinstance(group,dict) or set(group)!={'id','sample_panel','coordinate_ids','background_controls','laws'}:raise ValueError('Unknown profile fields.')
        if not isinstance(group['id'],str) or group['id'] in identifiers:raise ValueError('Profile identifiers must be unique strings.')
        identifiers.add(group['id']);panel=group['sample_panel']
        if not isinstance(panel,dict) or set(panel)-set(taxa):raise ValueError('Samples must attach to the SAME original taxa.')
        labels=[]
        for tip,copies in panel.items():
            if not isinstance(copies,list) or not copies or any(not isinstance(v,str) or not v for v in copies):raise ValueError('Fixed original-tip sample labels required.')
            labels.extend(copies)
        if not labels or len(labels)!=len(set(labels)):raise ValueError('Copy labels must be nonempty and unique within each panel.')
        bg=group['background_controls']
        if not isinstance(bg,dict) or request['protected_site'] in bg or any(not isinstance(k,str) or type(v) is not int or v not in (0,1) for k,v in bg.items()):raise ValueError('One SAME background programme for all three rows; marked site cannot be overridden there.')
        names=group['coordinate_ids']
        if not isinstance(names,list) or not names or len(set(names))!=len(names) or any(not isinstance(v,str) for v in names):raise ValueError('Shared finite event coordinate order required.')
        laws=group['laws']
        if not isinstance(laws,dict) or set(laws)!={'natural','force0','force1'}:raise ValueError('Natural and both original forcing rows required.')
        vectors={}
        for key,values in laws.items():
            if not isinstance(values,list) or len(values)!=len(names) or any(type(v) is not int and not isinstance(v,str) for v in values):raise ValueError('Exact rational probability vectors required; no truncation/floats.')
            q=[F(v) for v in values]
            if sum(q)!=1 or any(v<0 for v in q):raise ValueError('Every declared complete exact-law vector must normalize and be nonnegative.')
            vectors[key]=q
        for i,name in enumerate(names):
            coordinates.append([group['id'],name]);a.append(vectors['natural'][i]-vectors['force1'][i]);b.append(vectors['force0'][i]-vectors['force1'][i])
    return a,b,coordinates

def solve(request):
    try:a,b,coordinates=admitted(request)
    except (ValueError,TypeError,KeyError,ZeroDivisionError) as e:return {'status':'UNKNOWN_UNADMITTED_PROFILE','reason':str(e),'empirical_admission_claimed':False}
    if 'common' not in request['mechanisms']:
        return {'status':'UNKNOWN_COMMON_RULE_DOES_NOT_COVER_INDEPENDENT','empirical_admission_claimed':False}
    proof=None
    nonzero=next((i for i,x in enumerate(b) if x),None)
    if nonzero is None:
        witness=next((i for i,x in enumerate(a) if x),None)
        if witness is not None:proof={'kind':'FORCED_ROWS_EQUAL_NATURAL_DIFFERS','coordinate':witness,'nonzero_difference':str(a[witness])}
    else:
        i=nonzero;gamma=a[i]/b[i]
        for j in range(len(a)):
            minor=a[i]*b[j]-a[j]*b[i]
            if minor:
                proof={'kind':'NONZERO_SHARED_PARAMETER_MINOR','coordinates':[i,j],'minor_value':str(minor)};break
        if proof is None and not 0<gamma<1:
            proof={'kind':'COMMON_INTERIOR_PARAMETER_VIOLATION','coordinate':i,'forced_gamma':str(gamma)}
    base={'schema':'unknown-size-common-intervention-certificate-v1','source_contract':CONTRACT,
          'request_sha256':hashlib.sha256(json.dumps(request,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
          'protected_original_site':request['protected_site'],'coordinate_order':coordinates,
          'rule':'For ONE SAME0<gamma_H<1, natural=gamma_H*force0+(1-gamma_H)*force1 in EVERY profile/coordinate.',
          'graph_size_bound_used':False,'catalogue_enumeration_used':False,
          'exact_check':'Python Fraction arithmetic; no backend QE','empirical_admission_claimed':False,
          'Lean_certification_claimed':False,'general_G3_stopping_claimed':False}
    if proof is None:
        return {**base,'status':'UNKNOWN_PASSES_NECESSARY_COMMON_INTERVENTION_TEST','source_SAT_claimed':False}
    return {**base,'status':'GLOBAL_UNKNOWN_SIZE_UNSAT_FOR_DECLARED_COMMON_MODEL' if request['mechanisms']==['common'] else 'UNKNOWN_UNION_COMMON_COMPONENT_EXCLUDED_INDEPENDENT_UNCHECKED',
            'common_component_status':'GLOBAL_UNKNOWN_SIZE_UNSAT','proof':proof,'independent_component_status':'UNCHECKED' if 'independent' in request['mechanisms'] else 'NOT_REQUESTED'}

def main():
    p=argparse.ArgumentParser();p.add_argument('request');p.add_argument('--output',required=True);a=p.parse_args();out=solve(json.loads(Path(a.request).read_bytes()));Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
