#!/usr/bin/env python3
"""Validate a dated source-binding intake; never adopt bindings or run proof sources."""
import argparse,hashlib,json,pathlib,re,subprocess,collections
p=argparse.ArgumentParser();p.add_argument('--repo',type=pathlib.Path,required=True);p.add_argument('--inventory',type=pathlib.Path,required=True);a=p.parse_args();d=json.loads(a.inventory.read_text());r=a.repo.resolve();sha=lambda b:hashlib.sha256(b).hexdigest();canonical=json.loads((r/'docs/claims.json').read_bytes());cc={x['id']:x for x in canonical['claims']};table=json.loads((r/'packages/research/integration/claims.json').read_bytes());unbound={x['claim_id'] for x in table['claims'] if not x.get('lean',{}).get('module')};assert len(unbound)==70;assert sha((r/'docs/claims.json').read_bytes())==d['canonical_claims_sha256'];assert sha((r/'packages/research/integration/claims.json').read_bytes())==d['integration_claims_sha256'];rows=d['claims'];assert len(rows)==70 and {x['claim_id'] for x in rows}==unbound and len({x['claim_id'] for x in rows})==70
for x in rows:
 c=cc[x['claim_id']];assert x['exact_canonical_scope']==c['exact_statement_and_scope'];assert x['canonical_mathematical_status_unchanged']==c['mathematical_status'];assert x['canonical_completion_unchanged']==c['completion'];assert x['binding_adopted'] is False and x['claim_status_change'] is False and x['package_lean_module'] is None
sources={}
for n,x in d['modules'].items():
 assert x['module']==n and not pathlib.PurePosixPath(x['source_path']).is_absolute() and '..' not in pathlib.PurePosixPath(x['source_path']).parts
 b=subprocess.check_output(['git','-C',str(r),'show',d['package_public_source_commit']+':'+x['source_path']]);assert sha(b)==x['source_sha256'];assert hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==x['git_blob'];sources[n]=b.decode()
for x in rows:
 for candidate in x['candidate_qualified_reuse']:
  s=sources[candidate['module']]
  for e in candidate['candidate_declarations']:
   assert re.search(r'\b(?:theorem|lemma|def|abbrev|structure|instance)\s+'+re.escape(e['spelling'])+r'(?=[\s(:])',s),e
assert len(sources)==55;assert d['counts']==dict(collections.Counter(x['inventory_workstream'] for x in rows));print(json.dumps({'status':'PASS','unbound_ids':70,'source_modules':55,'direct_principal_source_candidates':13,'canonical_bindings_modified':False,'proof_execution':False,'scope':'Inventory/source identity validation, not scientific or kernel acceptance.'}))
