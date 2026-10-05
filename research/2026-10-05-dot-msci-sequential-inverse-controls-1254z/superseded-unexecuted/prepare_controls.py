"""Generate only the frozen arithmetic requests; execution requires the next review gate."""
import argparse,json,hashlib
from fractions import Fraction as F
from pathlib import Path
BASE=Path(__file__).resolve().parent
SPEC_SHA='7c2bdbe8d30826cccf7becd0e193527634c039ca68095afe5a0df0b694729d87'
REFERENCE=BASE.parent/'msci-330-feature-public-20261005-1039z/evaluator/CONTROL-RESULTS.json'
REFERENCE_SHA='acf3a3cfe6addaa79a29106c3aca9985e5247b18e4c31b41a50ff0d9e8552c6a'
def write_new(path,data):
    raw=(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n').encode()
    with Path(path).open('xb') as out:out.write(raw)
    return hashlib.sha256(raw).hexdigest()
def prepare(folder,spec_sha):
    import seq_engine as e
    import interval_math as m
    import contractors as ops
    if spec_sha!=SPEC_SHA:raise ValueError('unreviewed arithmetic specification')
    spec=e.read_json(BASE/'CONTROL-SPEC.json',SPEC_SHA);reference=e.read_json(REFERENCE,REFERENCE_SHA)
    folder=Path(folder);folder.mkdir(exist_ok=False)
    def physical(p):return {key:p[key] for key in ops.PHYSICAL if key not in ('u','v')}|{'u':p['t1']-p['h'],'v':p['t0']-p['t1']}
    truth={};means={}
    for name,provider_name in [('distinct','distinct_rates'),('equal','equal_rates')]:
        fixture=reference['fixtures'][provider_name];p={key:F(value) for key,value in fixture['parameters'].items()};truth[name]=physical(p)
        means[name]={key:m.I(F(fixture['features'][key[:-1]][int(key[-1])-1]['mean_interval']['lower']),F(fixture['features'][key[:-1]][int(key[-1])-1]['mean_interval']['upper'])) for key in m.FEATURES}
    x={key:e.legacy.rational(value) for key,value in spec['new_arithmetic_source'].items()}
    if set(x)!=set(ops.PHYSICAL):raise ValueError('new fixture all nine coordinates')
    p={key:x[key] for key in ('h','rA','rB','rC','rAB','rR','g')}|{'t1':x['h']+x['u'],'t0':x['h']+x['u']+x['v']}
    p,moments,shifted=m.forward.evaluate(p,spec['new_forward_output_bits']);truth['new']=x
    means['new']={key:shifted[key[:-1]][int(key[-1])-1] for key in m.FEATURES}
    new_output={'parameters':{key:str(value) for key,value in p.items()},'forward_sha256':m.SOURCE_SHA,'bits':spec['new_forward_output_bits'],'moments':{pair:[value.record() for value in rows] for pair,rows in moments.items()},'means':{pair:[value.record() for value in rows] for pair,rows in shifted.items()}}
    new_hash=write_new(folder/'NEW-ARITHMETIC-FORWARD.json',new_output)
    domain=e.legacy.parse_box(spec['physical_domain'])
    for point in truth.values():
        for key,(lo,hi) in zip(ops.PHYSICAL,domain):
            if not lo<point[key]<hi:raise ValueError('planted point is not strictly interior in every coordinate')
    records=[]
    for control in spec['controls']:
        kind=control['observations']
        if kind=='published_distinct':selected=means['distinct'];sources=['distinct']
        elif kind=='published_equal':selected=means['equal'];sources=['equal']
        elif kind=='hull_distinct_and_new':selected={key:m.I(min(means['distinct'][key].lo,means['new'][key].lo),max(means['distinct'][key].hi,means['new'][key].hi)) for key in m.FEATURES};sources=['distinct','new']
        elif kind=='unit_box':selected={key:m.I(0,1) for key in m.FEATURES};sources=['distinct','equal','new']
        elif kind=='AC1_9over10_AC2_3over5_rest_unit':selected={key:m.I(0,1) for key in m.FEATURES};selected['AC1']=m.I.point(F(9,10));selected['AC2']=m.I.point(F(3,5));sources=[]
        else:raise ValueError('unreviewed observation kind')
        budget={key:control[key] for key in ('max_operations','max_splits','sweeps_per_cell')}|{'max_depth':2,'wall_ms':10000,'recovery_wall_ms':10000,'recovery_max_operations':64}
        request={'schema':e.SCHEMA,'model':e.MODEL,'quantity':'shifted_bernoulli_character_mean','box':spec['physical_domain'],'features':{key:[str(value.lo),str(value.hi)] for key,value in selected.items()},'budget':budget,'provenance':{'kind':'deterministic_arithmetic_constraints','spec_sha256':SPEC_SHA,'published_fixture_sha256':REFERENCE_SHA,'new_arithmetic_output_sha256':new_hash,'compatible_source_ids_for_external_controls_only':sources,'statistical_coverage_claimed':False}}
        filename=control['name']+'.json';identity=write_new(folder/filename,request);e.read_request(folder/filename,identity);records.append({'name':control['name'],'request':filename,'sha256':identity,'truth_ids':sources})
    truth_hash=write_new(folder/'TRUTH-FIXTURES.json',{'physical':{name:{key:str(value) for key,value in point.items()} for name,point in truth.items()},'selected_certified_means':{name:{key:value.record() for key,value in vector.items()} for name,vector in means.items()},'new_arithmetic_output_sha256':new_hash,'spec_sha256':SPEC_SHA})
    write_new(folder/'CONTROL-MANIFEST.json',{'controls':records,'truth_sha256':truth_hash,'new_arithmetic_output_sha256':new_hash,'spec_sha256':SPEC_SHA,'statistical_coverage_claimed':False})
    return {'status':'ARITHMETIC_REQUESTS_PREPARED','controls':len(records),'new_arithmetic_output_sha256':new_hash,'truth_sha256':truth_hash,'actual_filter_runs':0}
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',required=True);parser.add_argument('--spec-sha256',required=True);parser.add_argument('--source-manifest',required=True);parser.add_argument('--source-manifest-sha256',required=True);a=parser.parse_args()
    import sequential_runner as runner
    runner.authenticate(a.source_manifest,a.source_manifest_sha256)
    print(json.dumps(prepare(a.output,a.spec_sha256),sort_keys=True,indent=2))
