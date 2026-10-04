#!/usr/bin/env python3
"""Validate delivered scientific source/evidence bytes, without executing proof code.
Kernel replay is separate: use the pinned Lake reproduction instructions.
"""
from pathlib import Path
import gzip,hashlib,json,re
root=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((root/'PUBLIC-MANIFEST.json').read_text())
expected={r['path'] for r in manifest['files']}|{'PUBLIC-MANIFEST.json'}
actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
assert actual==expected,(actual-expected,expected-actual)
for row in manifest['files']:
 data=(root/row['path']).read_bytes()
 assert len(data)==row['bytes'] and H(data)==row['sha256'],row['path']
reg=json.loads((root/'SOURCE-REGISTRY.json').read_text())
assert reg['source_modules']==reg['present_source_modules']==len(reg['records'])==467
sources={r['module']:r for r in reg['records']}
assert len(sources)==467
for m,row in sources.items():
 data=(root/row['path']).read_bytes();assert len(data)==row['bytes'] and H(data)==row['sha256']
 for line in data.decode().splitlines():
  if line.startswith('import '):
   for dep in line[7:].split():
    if dep.startswith(('G1','G2','G3','G4','G5','G6','G7','GProgram','Source','Graph','UnifiedLean.')):
     assert dep in sources,(m,dep)
bind=json.loads((root/'certificate/SOURCE-OBJECT-IMPORT-BINDINGS.json').read_text())
assert len(bind['rows'])==467
for row in bind['rows']:
 assert row['source_sha256']==sources[row['module']]['sha256']
 assert row['exit_code']==0 and row['compiler_binary_sha256']==manifest['compiler_binary_sha256']
 for imp in row['direct_import_artifacts']:
  if imp['module'] in sources:
   provider=next(x for x in bind['rows'] if x['module']==imp['module'])
   assert imp['sha256']==provider['object_sha256']
for kind in ['AXIOMS','COMBINED-AXIOMS']:
 report=json.loads(gzip.decompress((root/f'certificate/{kind}-DECLARATIONS.json.gz').read_bytes()))
 assert not report['nonstandard_axiom_rows'] and not report['missing_modules']
 assert not [r for r in report['declarations'] if r['kind']=='axiom']
receipt=json.loads((root/'certificate/BUILD-RECEIPT.json').read_text())
assert receipt['owned_declarations']==28 and receipt['complete_closure_declarations']==8016
assert receipt['fresh_final_components']==4 and receipt['matched_checked_provider_components']==463
assert not receipt['all467_sources_freshly_rebuilt_in_new_flat_layout']  # historical guard/provider receipt
assert manifest['new_full_flat_layout_build_claimed']
fresh=json.loads((root/'certificate/fresh/SERIAL-BUILD-RECEIPT.json').read_text())
assert fresh['exit_code']==0 and fresh['fresh_proof_source_targets']==len(fresh['records'])==467
assert not fresh['inherited_proof_objects_installed'] and fresh['source_modules_unchanged']
assert fresh['default_check']['exit_code']==0
logs=json.loads(gzip.decompress((root/'certificate/fresh/TARGET-LOGS.json.gz').read_bytes()))
logmap={r['module']:r for r in logs}; assert len(logmap)==467
for r in fresh['records']:
 assert r['source_sha256']==sources[r['module']]['sha256']
 assert r['exit_code']==0 and r['log_sha256']==logmap[r['module']]['raw_sha256']
 assert H(logmap[r['module']]['text'].encode())==logmap[r['module']]['public_sha256']
build_bindings=json.loads(gzip.decompress((root/'certificate/fresh/FRESH-OBJECT-IMPORT-BINDINGS.json.gz').read_bytes()))
newobjects={r['module']:r['fresh_object_sha256'] for r in build_bindings['rows']}
assert len(newobjects)==467
for r in build_bindings['rows']:
 assert r['source_sha256']==sources[r['module']]['sha256']
 for dep in r['direct_import_artifacts']:
  if dep['module'] in newobjects: assert dep['sha256']==newobjects[dep['module']]
fresh_audit=json.loads(gzip.decompress((root/'certificate/fresh/FRESH-CLOSURE-AUDIT.json.gz').read_bytes()))
assert set(fresh_audit['selected_modules'])==set(sources)
assert fresh_audit['declaration_count']==8016 and fresh_audit['theorem_declaration_count']==5397
assert not fresh_audit['owned_axioms'] and not fresh_audit['nonstandard_axiom_rows'] and not fresh_audit['missing_modules']
projection=json.loads((root/'FRESH-EVIDENCE-PROJECTION.json').read_text())
for r in projection['records']:
 payload=(root/r['path']).read_bytes(); assert H(payload)==r['delivered_sha256']
 decoded=gzip.decompress(payload) if r['deterministic_gzip'] else payload
 assert H(decoded)==r['public_decoded_sha256']
ack=json.loads((root/'reviews/ORIGINAL-MASTER-ACK.json').read_text())
assert ack['status']=='ACCEPTED_FULL_ORIGINAL_G1_MASTER_WITH_ALL_N_SHARPNESS'
assert ack['remaining_original_G1_contract_obligation'] is None
print(json.dumps({'delivered_byte_certificate':'PASS','exact_mathematical_sources':467,
 'fresh_final_components':4,'matched_checked_providers':463,'full_closure_declarations':8016,
 'original_master_semantic_acceptance':True,'new_flat_layout_full_rebuild_claimed':True,'fresh_source_targets':467,'separate_default_Lake_exit':0,'fresh_full_closure_audit':True},indent=2))
