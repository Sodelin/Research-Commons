#!/usr/bin/env python3
"""Check public bytes and recorded certificates, without compiler execution."""
from pathlib import Path
import json,gzip,hashlib
R=Path(__file__).resolve().parent
def sha(b):return hashlib.sha256(b).hexdigest()
def git(b):return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
def read(p):return json.loads((R/p).read_bytes())
def main():
 m=read('SOURCE-MANIFEST.json');expected={r['path']:r for r in m['files']}
 actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file() and p.name!='SOURCE-MANIFEST.json' and '__pycache__' not in p.parts}
 assert actual==set(expected)
 for p,r in expected.items():
  b=(R/p).read_bytes();assert sha(b)==r['sha256'] and len(b)==r['bytes'] and git(b)==r['git_blob_sha'],p
 idx=read('ACCEPTED-CHECKPOINT-INDEX.json');assert len(idx['profiles'])==19 and idx['independently_accepted_successor_modules']==127 and not idx['combined_952_test_claimed']
 modules=[];reports=0
 for profile in idx['profiles']:
  for r in profile['source_object_receipt_bindings']:
   modules.append(r['module']);assert sha((R/r['source']).read_bytes())==r['source_sha256'];b=(R/r['public_receipt_path']).read_bytes();assert sha(b)==r['public_receipt_sha256'];c=json.loads(b)
   assert c['_public_projection']['raw_sha256']==r['receipt_sha256'] and c['exit_code']==0 and c['source_and_direct_imports_stable']
   assert c['source_sha256']==r['source_sha256'] and c['object_sha256']==r['object_sha256']
  for p in (R/profile['profile']).rglob('declarations.json*'):
   b=p.read_bytes();b=gzip.decompress(b) if p.suffix=='.gz' else b;c=json.loads(b);assert c['declaration_count']==len(c['declarations'])
   if 'nonstandard_axiom_rows' in c:
    assert not c['missing_modules'] and not c['nonstandard_axiom_rows'];assert all(set(x['axioms'])<= {'propext','Classical.choice','Quot.sound'} and x['kind']!='axiom' for x in c['declarations'])
   reports+=1
 assert len(modules)==len(set(modules))==127 and reports==76
 print(json.dumps({'status':'PASS_127_SOURCE_AND_RECORDED_FULL_AUDIT_BINDINGS','profiles':19,'sources':127,'full_reports':reports,'last_combined_tested_sources':825,'compiler_not_rerun':True}))
if __name__=='__main__':main()
