"""Pure exact-rational request preparation from already admitted arithmetic evidence."""
import json
from fractions import Fraction as F
from pathlib import Path
import seq_engine as e
BASE=Path(__file__).resolve().parent
SPEC_SHA='ce03abcadba28e4f95c51387ab7f361c80f4bf2e181d0245b6b38b17579f493f'
PRIOR=BASE.parent/'msci-sequential-inverse-implementation-20261005-1225z/fixture-preparation-attempt1/generated'
MANIFEST_SHA='9a5c172900d6eaa96114b25da6c809ab659fe59a0e42bdda8d8cb1fb6c521c42'
TRUTH_SHA='c0da835116a929a985a7270036b07a2ed5535d39827a9136bd0b4c2b81ca8315'
def write_new(path,data):
    raw=e.canonical(data)
    with Path(path).open('xb') as out:out.write(raw)
    return e.sha(raw)

def prepare(folder):
    spec=e.read_json(BASE/'CONTROL-SPEC.json',SPEC_SHA);prior=e.read_json(PRIOR/'CONTROL-MANIFEST.json',MANIFEST_SHA);truth=e.read_json(PRIOR/'TRUTH-FIXTURES.json',TRUTH_SHA)
    if spec['source_fixture_manifest_sha256']!=MANIFEST_SHA or spec['source_truth_sha256']!=TRUTH_SHA:raise ValueError('source fixture identities')
    references={entry['name']:entry for entry in prior['controls']};radius=e.legacy.rational(spec['local_half_width_all_nine_coordinates']);folder=Path(folder);folder.mkdir(exist_ok=False);records=[]
    for control in spec['controls']:
        reference=references[control['source_request']];original=e.read_json(PRIOR/reference['request'],reference['sha256']);box=original['box']
        if control['domain'].startswith('predetermined_local_'):
            source=control['domain'].removeprefix('predetermined_local_');point={key:F(value) for key,value in truth['physical'][source].items()};box={key:[str(point[key]-radius),str(point[key]+radius)] for key in e.ops.PHYSICAL}
            for key,(lo,hi) in zip(e.ops.PHYSICAL,e.legacy.parse_box(box)):
                if not lo<point[key]<hi:raise ValueError('local point not strictly interior')
        elif control['domain']!='original_broad':raise ValueError('undeclared domain mode')
        budget={key:control[key] for key in ('max_operations','max_splits','sweeps_per_cell','preconditioner')}|{'max_depth':2,'wall_ms':10000,'recovery_wall_ms':10000,'recovery_max_operations':16}
        request={'schema':e.SCHEMA,'model':e.MODEL,'quantity':original['quantity'],'box':box,'features':original['features'],'budget':budget,'provenance':{'kind':'reused_deterministic_arithmetic_constraints','spec_sha256':SPEC_SHA,'source_request_sha256':reference['sha256'],'source_fixture_manifest_sha256':MANIFEST_SHA,'source_truth_sha256':TRUTH_SHA,'domain_scope':control['domain'],'statistical_coverage_claimed':False}}
        name=control['name']+'.json';identity=write_new(folder/name,request);e.read_request(folder/name,identity);records.append({'name':control['name'],'request':name,'sha256':identity,'truth_ids':reference['truth_ids'],'domain_scope':control['domain']})
    with (folder/'TRUTH-FIXTURES.json').open('xb') as out:out.write((PRIOR/'TRUTH-FIXTURES.json').read_bytes())
    if e.sha((folder/'TRUTH-FIXTURES.json').read_bytes())!=TRUTH_SHA:raise ValueError('copied truth changed')
    manifest={'controls':records,'truth_sha256':TRUTH_SHA,'source_fixture_manifest_sha256':MANIFEST_SHA,'spec_sha256':SPEC_SHA,'new_source_point_evaluations':0,'new_biological_data_or_simulation':False}
    return write_new(folder/'CONTROL-MANIFEST.json',manifest)
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();print(prepare(a.output))
