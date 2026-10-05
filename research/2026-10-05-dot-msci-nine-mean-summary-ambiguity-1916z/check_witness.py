"""Two fixed coherent sources against one frozen interval summary; no sampling."""
from fractions import Fraction as F
from pathlib import Path
import argparse, hashlib, json, resource, sys, types
BASE=Path(__file__).resolve().parent
ROOT=BASE.parent
PROVIDER=ROOT/'msci-330-feature-public-20261005-1039z/evaluator/certified_forward.py'
PROVIDER_SHA='c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace'
RESULT=ROOT/'msci-model-semantic-public-20261005-1854z/integration/MODEL-CHECK-RESULTS-corrected.json'
RESULT_SHA='0a1a259ab45c69d3caff36e1ff024ab3310e78b84a6fd6f631e8388635662644'
REQUEST=ROOT/'msci-model-semantic-public-20261005-1854z/integration/declared-model/REQUEST.json'
REQUEST_SHA='aebcfdfe2caa31d842f56be70387b415fc9f8677aa8f8cd4a58ea62b83c82f30'
FEATURES=('AC1','AC2','CC1','BC1','BC2','AB1','AB2','AA1','BB1')
PHYSICAL=('h','u','v','rA','rB','rC','rAB','rR','g')
BITS=128

def read_exact(path,digest):
    if path.is_symlink() or path.stat().st_size>2*1024**2:raise ValueError('input type/size')
    raw=path.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=digest:raise ValueError('source/input identity mismatch')
    return raw

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--provider",type=Path,default=PROVIDER)
    parser.add_argument("--result",type=Path,default=RESULT)
    parser.add_argument("--request",type=Path,default=REQUEST)
    args=parser.parse_args()
    resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,256*1024**2))
    resource.setrlimit(resource.RLIMIT_CPU,(25,25))
    result=json.loads(read_exact(args.result,RESULT_SHA));request=json.loads(read_exact(args.request,REQUEST_SHA))
    if result['dataset_sha256']!=request['dataset_sha256'] or result['m']!=request['expected_loci'] or result['delta']!=request['delta']:raise ValueError('frozen request/result binding')
    if set(result['confidence_box'])!=set(FEATURES) or set(request['domain'])!=set(PHYSICAL):raise ValueError('fixed feature/domain schema')
    domain={key:tuple(F(v) for v in request['domain'][key]) for key in PHYSICAL}
    targets={key:F(request['normalized_width_targets'][key]) for key in PHYSICAL}
    if any(v!=F(1,20) for v in targets.values()):raise ValueError('original target changed')
    box={key:tuple(F(v) for v in result['confidence_box'][key]) for key in FEATURES}
    provider_bytes=read_exact(args.provider,PROVIDER_SHA)
    provider=types.ModuleType('_fixed_nine_mean_witness_provider')
    provider.__file__=str(args.provider);sys.modules[provider.__name__]=provider
    exec(compile(provider_bytes,str(args.provider),'exec'),provider.__dict__)
    records=[];selected=[]
    for label,rate in [('known_source',F(1)),('alternative_source',F(2))]:
        physical={'h':F(1,16),'u':F(1,16),'v':F(1,16),'rA':rate,'rB':F(2),'rC':F(4),'rAB':F(1),'rR':F(2),'g':F(1,4)}
        interior={key:domain[key][0]<physical[key]<domain[key][1] for key in PHYSICAL}
        if not all(interior.values()):raise ValueError('fixed witness outside admitted interior')
        absolute={key:physical[key] for key in ('h','rA','rB','rC','rAB','rR','g')}
        absolute.update(t1=physical['h']+physical['u'],t0=physical['h']+physical['u']+physical['v'])
        parsed,raw,means=provider.evaluate(absolute,BITS)
        values={key:means[key[:-1]][int(key[-1])-1] for key in FEATURES}
        if any(value.hi-value.lo>F(1,2**BITS) for value in values.values()):raise ValueError('certified width bound failed')
        containment={key:box[key][0]<=value.lo<=value.hi<=box[key][1] for key,value in values.items()}
        margins={key:[str(value.lo-box[key][0]),str(box[key][1]-value.hi)] for key,value in values.items()}
        records.append({'id':label,'physical':{k:str(v) for k,v in physical.items()},'absolute_times_and_rates':{k:str(v) for k,v in parsed.items()},'strict_domain_membership':interior,'shifted_mean_enclosures':{key:value.record() for key,value in values.items()},'full_nine_enclosure_containment':containment,'certified_endpoint_margins':margins})
        selected.append(values)
    separation=F(1);original_width=domain['rA'][1]-domain['rA'][0]
    limit=targets['rA']*original_width
    mean_separation=selected[1]['AA1'].lo-selected[0]['AA1'].hi
    success=all(all(record['full_nine_enclosure_containment'].values()) for record in records) and separation>limit and mean_separation>0
    output={'status':'CERTIFIED_INTERVAL_SUMMARY_AMBIGUITY' if success else 'NOT_CERTIFIED_NO_FURTHER_SEARCH',
      'provider_sha256':PROVIDER_SHA,'frozen_model_result_sha256':RESULT_SHA,'frozen_analysis_request_sha256':REQUEST_SHA,'dataset_sha256':result['dataset_sha256'],
      'feature_order':list(FEATURES),'original_confidence_box':result['confidence_box'],'sources':records,'output_precision_bits':BITS,'forward_evaluations':2,
      'rA_separation':str(separation),'rA_original_width':str(original_width),'rA_requested_width_limit':str(limit),'necessary_normalized_rA_cover_width':str(separation/original_width) if success else None,'normalized_goal':str(targets['rA']),
      'AA1_mean_separation_lower_bound':str(mean_separation),'other_eight_enclosures_byte_equivalent':all(selected[0][key].record()==selected[1][key].record() for key in FEATURES if key!='AA1'),
      'new_sampling_or_generation':False,'confidence_box_or_domain_modified':False,'identical_full_DNA_laws_claimed':False,'claim_scope':('Two distinct admitted sources fit this same nine-mean interval summary; every all-compatible-source cover exceeds its rA width target.' if success else 'Witness not certified; no ambiguity conclusion.')}
    encoded=json.dumps(output,sort_keys=True,indent=2)+'\n'
    if len(encoded.encode())>2*1024**2:raise ValueError('output cap')
    print(encoded,end='')
if __name__=='__main__':main()
