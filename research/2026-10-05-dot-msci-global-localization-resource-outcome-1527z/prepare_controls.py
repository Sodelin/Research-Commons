"""Exact original-domain request preparation; no forward/AD/numerical localization."""
from pathlib import Path
import global_engine as e
BASE=Path(__file__).resolve().parent
SPEC_SHA='76b1418a82876ce38fd29bbfce049382ee407e548bb97a9b9acc05f6276355c6'
PRIOR=BASE.parent/'msci-sequential-inverse-implementation-20261005-1225z/fixture-preparation-attempt1/generated'
MANIFEST_SHA='9a5c172900d6eaa96114b25da6c809ab659fe59a0e42bdda8d8cb1fb6c521c42'
TRUTH_SHA='c0da835116a929a985a7270036b07a2ed5535d39827a9136bd0b4c2b81ca8315'
def write_new(path,data):
    raw=e.canonical(data)
    with Path(path).open('xb') as out:out.write(raw)
    return e.sha(raw)
def prepare(folder):
    spec=e.read_json(BASE/'CONTROL-SPEC.json',SPEC_SHA);old=e.read_json(PRIOR/'CONTROL-MANIFEST.json',MANIFEST_SHA);truth=e.read_json(PRIOR/'TRUTH-FIXTURES.json',TRUTH_SHA)
    if spec['source_fixture_manifest_sha256']!=MANIFEST_SHA or spec['source_truth_sha256']!=TRUTH_SHA:raise ValueError('prior fixture identities')
    references={entry['name']:entry for entry in old['controls']};folder=Path(folder);folder.mkdir(exist_ok=False);records=[]
    for control in spec['controls']:
        reference=references[control['source_request']];original=e.read_json(PRIOR/reference['request'],reference['sha256'])
        budget={key:control[key] for key in ('scalar_steps','max_stages','max_splits','max_states','max_depth')}|{'wall_ms':spec['wall_ms'],'recovery_wall_ms':spec['recovery_wall_ms'],'recovery_max_stages':control['max_stages']}
        request={'schema':e.SCHEMA,'model':e.MODEL,'quantity':original['quantity'],'box':original['box'],'features':original['features'],'normalized_width_targets':spec['normalized_width_targets'],'budget':budget,'provenance':{'kind':'original_broad_deterministic_arithmetic_constraints','source_request_sha256':reference['sha256'],'source_fixture_manifest_sha256':MANIFEST_SHA,'source_truth_sha256':TRUTH_SHA,'spec_sha256':SPEC_SHA,'original_domain_preserved':True,'statistical_coverage_claimed':False}}
        name=control['name']+'.json';identity=write_new(folder/name,request);parsed=e.read_request(folder/name,identity)
        if request['box']!=original['box'] or any(value.width<=0 for value in parsed['physical'].values()):raise ValueError('original all-nine domain not preserved')
        records.append({'name':control['name'],'request':name,'sha256':identity,'source_request_sha256':reference['sha256'],'truth_ids':reference['truth_ids'],'domain_scope':'original_broad'})
    with (folder/'TRUTH-FIXTURES.json').open('xb') as out:out.write((PRIOR/'TRUTH-FIXTURES.json').read_bytes())
    if e.sha((folder/'TRUTH-FIXTURES.json').read_bytes())!=TRUTH_SHA:raise ValueError('truth copy changed')
    return write_new(folder/'CONTROL-MANIFEST.json',{'controls':records,'truth_sha256':TRUTH_SHA,'source_fixture_manifest_sha256':MANIFEST_SHA,'spec_sha256':SPEC_SHA,'new_parameter_vectors':False,'smaller_supplied_domains':False,'statistical_coverage_claimed':False})
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();print(prepare(a.output))
