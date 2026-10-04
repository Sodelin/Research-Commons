#!/usr/bin/env python3
"""Verify delivered files and recorded Lean evidence; fresh checking is lake test."""
from pathlib import Path
import gzip,hashlib,json
ROOT=Path(__file__).resolve().parents[1]
STANDARD={'propext','Classical.choice','Quot.sound'}
def sha(b):return hashlib.sha256(b).hexdigest()
def git(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads((ROOT/p).read_bytes())
def main():
 m=read('SOURCE-MANIFEST.json');files={r['path']:r for r in m['files']}
 actual={str(p.relative_to(ROOT)) for p in ROOT.rglob('*') if p.is_file() and not any(x in p.relative_to(ROOT).parts for x in ['.build','.lake','__pycache__']) and p.name!='SOURCE-MANIFEST.json'}
 assert actual==set(files),actual^set(files)
 for p,r in files.items():
  b=(ROOT/p).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'] and git(b)==r['git_blob_sha'],p
 registry=read('catalog/SOURCE-REGISTRY.json')['records'];assert len(registry)==825
 bindings=read('certificate/SOURCE-OBJECT-RECEIPT-BINDINGS.json')['records'];bykey={(r['profile'],r['module']):r for r in bindings}
 assert len(bykey)==825
 for r in registry:
  assert sha((ROOT/r['source']).read_bytes())==r['source_sha256']
  b=bykey[r['profile'],r['module']];assert b['source_sha256']==r['source_sha256']
  raw=(ROOT/b['public_receipt_path']).read_bytes();assert sha(raw)==b['public_receipt_sha256']
  c=json.loads(raw);assert c['_public_projection']['raw_sha256']==b['raw_receipt_sha256']==b['receipt_sha256']
  assert c['exit_code']==0 and c['status'].startswith('PASS')
  assert c['source_sha256']==r['source_sha256'] and c['object_sha256']==b['object_sha256']
  assert c['source_and_direct_imports_stable'] and c['direct_import_sha256']==b['direct_import_sha256']
 summary=read('certificate/AUDIT-SUMMARY.json');assert len(summary)==32
 for r in summary:
  b=gzip.decompress((ROOT/r['report_path']).read_bytes());assert sha(b)==r['public_report_uncompressed_sha256']
  c=json.loads(b);assert c['_public_projection']['raw_sha256']==r['raw_report_sha256']
  assert c['declaration_count']==r['declarations']==len(c['declarations'])
  if r['kind']=='axioms':
   assert not c['missing_modules']
   assert not c['nonstandard_axiom_rows'] and not [x for x in c['declarations'] if x['kind']=='axiom']
   assert all(set(x['axioms'])<=STANDARD for x in c['declarations'])
  else:assert not c.get('nonstandard_dependency_rows',[])
 terminal=read('certificate/G1-CANONICAL21-LAKE-TEST-TERMINAL-RECEIPT.json')
 assert terminal['command']==['lake','test'] and terminal['exit_code']==0 and terminal['active_source_records']==825
 stdout=(ROOT/'certificate/G1-CANONICAL21-LAKE-TEST.stdout').read_bytes()
 assert sha(stdout)==terminal['stdout_sha256']
 for p,h in terminal['source_config_sha256'].items():assert sha((ROOT/p).read_bytes())==h,p
 print(json.dumps({'status':'PASS_DELIVERED_825_SOURCE_AND_RECORDED_CERTIFICATES','delivered_files':len(files)+1,'source_records':825,'complete_reports':32,'recorded_lake_test_exit_code':0,'compiler_rerun_by_hash_verifier':False}))
if __name__=='__main__':main()
