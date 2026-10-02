#!/usr/bin/env python3
"""Copy and hash-check one successful guard into an immutable version snapshot."""
from pathlib import Path
import json,hashlib,shutil,datetime,sys
ROOT=Path(__file__).resolve().parents[1]
receipt=ROOT/sys.argv[1]/'receipt.json';d=json.loads(receipt.read_text())
assert d['status']=='PASS_SELECTED_LAKE_IMPORT_CLOSURE' and d['source_and_config_stable']
version=sys.argv[2];S=ROOT/'snapshots'/version;S.mkdir(parents=True)
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for p,v in d['source_and_config_sha256'].items():
 q=ROOT/p;t=S/p;t.parent.mkdir(parents=True,exist_ok=True);assert h(q)==v;shutil.copyfile(q,t);assert h(t)==v
for m,v in d['artifact_sha256'].items():
 q=ROOT/'.lake/build/lib/lean'/Path(*m.split('.')).with_suffix('.olean');t=S/'objects'/Path(*m.split('.')).with_suffix('.olean');t.parent.mkdir(parents=True,exist_ok=True);assert h(q)==v;shutil.copyfile(q,t);assert h(t)==v
for p in [receipt,receipt.parent/'build.log',ROOT/'catalog/COMBINED-IMPORT-BASELINE.json']:
 t=S/('receipt.json' if p==receipt else 'build.log' if p.name=='build.log' else 'catalog/COMBINED-IMPORT-BASELINE.json');t.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,t)
f={'version':version,'frozen_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'modules':d['module_count_excluding_aggregate'],'guarded_pass':True,'source_and_config_sha256':d['source_and_config_sha256'],'artifact_sha256':d['artifact_sha256'],'receipt_directory':d['receipt_directory'],'printed_axiom_audits':d['printed_axiom_audits'],'axiom_audit_count_is_distinct_theorem_count':False,'full_project_source_correctness_claim':False,'historical_source_coverage_complete_claim':False}
(S/'FREEZE.json').write_text(json.dumps(f,indent=2)+'\n');print('Frozen',version,len(f['source_and_config_sha256']),'source/config and',len(f['artifact_sha256']),'objects')
