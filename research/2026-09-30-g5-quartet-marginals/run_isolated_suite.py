"""Sequential process-isolated fixture replay and exact aggregate receipts.

This avoids retaining symbolic caches for unrelated fixture cases. It does
not dispatch research agents, enumerate source classes, or run in background.
"""
from pathlib import Path
import gzip, hashlib, json, os, subprocess, sys, time
from metric_partition_inverse import supplied_fixtures
from new_fixtures import stress_sources

HERE=Path(__file__).resolve().parent
OUT=HERE/'isolated-suite'
OUT.mkdir(exist_ok=True)
started=time.time()
reports=[];fixtures={};observations=[];certificates=[];execution=[]
for i,source in enumerate(supplied_fixtures()+stress_sources()):
    for mode in ('common','independent'):
        case_id=f'case-{len(reports):03d}'
        target=OUT/case_id;target.mkdir(exist_ok=True)
        env=dict(os.environ,G5_CASE_FILTER=source.name+'/'+mode,G5_OUTPUT_DIR=str(target))
        receipt_path=target/'quartet-checks.json'
        report=json.loads(receipt_path.read_text()) if receipt_path.exists() else {}
        reusable=(report.get('status')=='PASS' and report.get('case_filter')==source.name+'/'+mode
                  and all(report.get('payload_sha256',{}).get(name)==hashlib.sha256((HERE/name).read_bytes()).hexdigest()
                          for name in ('metric_partition_inverse.py','quartet_target.py','new_fixtures.py','verify_quartet_target.py')))
        if not reusable:
            with (target/'execution.log').open('w') as f:
                result=subprocess.run([sys.executable,'-B',str(HERE/'verify_quartet_target.py')],
                                      env=env,cwd=HERE,stdout=f,stderr=subprocess.STDOUT,timeout=50)
            if result.returncode:
                raise RuntimeError(f'{case_id} did not complete; see its execution.log')
            report=json.loads(receipt_path.read_text())
        if report['status']!='PASS' or len(report['cases'])!=1:
            raise AssertionError('Incomplete or unexpected per-case report')
        item=report['cases'][0];item['case_id']=case_id
        reports.append(report)
        for entry in json.loads((target/'quartet-fixtures.json').read_text()):fixtures[entry['name']]=entry
        execution.append({'case_id':case_id,'fixture':source.name,'mode':mode,'exit_code':0,'reused_verified_receipt':reusable,
                          'receipt_sha256':hashlib.sha256((target/'quartet-checks.json').read_bytes()).hexdigest()})
        print(case_id,source.name,mode,'PASS',item['quartets'],'quartets',flush=True)
        (OUT/'progress.json').write_text(json.dumps(execution,indent=2)+'\n')
aggregate={'status':'PASS','session':'G5-QUARTET-MARGINALS-20260930',
           'evidence':'Author-run exact finite tests and serialized-germ replay; not independent acceptance or all-size proof.',
           'source_fixtures':len(fixtures),'inheritance_mode_cases':len(reports),
           'python':reports[0]['python'],'sympy':reports[0]['sympy'],'networkx':reports[0]['networkx'],
           'source_scope':reports[0]['scope'],'input_domain':reports[0]['input_domain'],
           'cases':[r['cases'][0] for r in reports], 'executions':execution}
for key in ('total_quartet_runs','total_source_generated_germ_certificates',
            'total_source_free_replay_germ_certificates','total_boundary_checks',
            'quartet_cluster_comparisons','source_free_replays','input_and_resource_guards'):
    aggregate[key]=sum(r[key] for r in reports)
for key in ('max_selected_tips_per_germ','max_spectral_atoms','max_derivative_order'):
    aggregate[key]=max(r[key] for r in reports)
aggregate['distinct_guard_types']=6
aggregate['input_and_resource_guards_note']='Six structural/input guards repeated in each isolated case, not distinct biological cases.'
aggregate['highest_fixture_level']=max(f['admission']['level'] for f in fixtures.values())
aggregate['not_claimed']=reports[0]['not_claimed']
aggregate['elapsed_seconds']=round(time.time()-started,3)
(OUT/'fixtures.json').write_text(json.dumps(list(fixtures.values()),indent=2)+'\n')
# Merge archives only AFTER every child process has finished, one case at a
# time. Keeping all decoded JSON beside a symbolic child needlessly doubled
# peak memory in the original test harness; it is not part of the inverse.
for destination,source_name in [('observations.json.gz','quartet-observations.json.gz'),
                                ('certificates.json.gz','quartet-certificates.json.gz')]:
    with (OUT/destination).open('wb') as raw:
        with gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as gz:
            gz.write(b'[');first=True
            for entry_info in execution:
                case_id=entry_info['case_id']
                entries=json.loads(gzip.decompress((OUT/case_id/source_name).read_bytes()))
                for entry in entries:
                    entry['case_id']=case_id
                    if not first:gz.write(b',')
                    gz.write(json.dumps(entry,separators=(',',':')).encode())
                    first=False
            gz.write(b']')
aggregate['artifact_sha256']={name:hashlib.sha256((OUT/name).read_bytes()).hexdigest()
                            for name in ('fixtures.json','observations.json.gz','certificates.json.gz')}
aggregate['code_sha256']={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in HERE.glob('*.py')}
(OUT/'checks.json').write_text(json.dumps(aggregate,indent=2)+'\n')
print('AGGREGATE',json.dumps({k:v for k,v in aggregate.items() if k.startswith('total_') or k.startswith('max_') or k in ('source_fixtures','inheritance_mode_cases','elapsed_seconds')}),flush=True)
