#!/usr/bin/env python3
"""Offline intake of exact owner-authorized public canonical-reference bodies.

No network, execution, private repository discovery or scientific status writes.
"""
import argparse, collections, hashlib, json, pathlib, re, subprocess, urllib.parse

PINS = {
 'Sodelin/Work-on-Samuel-Alexander-Research-':'e2502c82ab9a77c00543932f775a71e5374221f7',
 'Sodelin/Formalizing-Soft-Sciences':'8e665d2a9f6168e6448b2ca49fccbec87d57d3ad',
 'Sodelin/Cross-Scale-Causal-Formalization':'28bdb75b8d057332e1bb32020d02e5eaea4c0517',
 'Sodelin/Collatz-Conjecture-Work':'026aa4ad4be6453a005ab950b160a9f2204c5271',
}
ROLE='Source body only; no scientific status, review, execution or license acceptance inferred.'

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--verified-inputs',type=pathlib.Path,required=True);p.add_argument('--references',type=pathlib.Path,required=True);p.add_argument('--body-root',type=pathlib.Path,required=True);p.add_argument('--repo',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
 inputs=json.loads(a.verified_inputs.read_bytes());refs=json.loads(a.references.read_bytes());by_url={r['reference']:r for r in inputs['records']};documents=[];unavailable=[]
 # Public visibility is a recovered API observation, not a licensing assertion.
 checks={r['repository']:r for r in inputs['repository_checks']}
 for repo in PINS:
  assert checks[repo]['private'] is False and checks[repo]['visibility']=='public', 'Missing public input observation'
 for ref in refs['records']:
  if ref['coverage']=='bundled_selected_full_text':continue
  url=ref['reference'];parsed=urllib.parse.urlsplit(url);normalized=urllib.parse.urlunsplit((parsed.scheme,parsed.netloc,parsed.path,'',''));match=re.fullmatch(r'https://github.com/([^/]+/[^/]+)/blob/([a-f0-9]{40})/(.+)',normalized)
  if not match:continue
  repo,pin,encoded=match.groups();path=urllib.parse.unquote(encoded);parts=pathlib.PurePosixPath(path)
  assert not parts.is_absolute() and '..' not in parts.parts and '\\' not in path
  if repo in PINS:
   assert pin==PINS[repo], 'Unreviewed first-party revision'
   source=by_url.get(url)
   if not source or source['status']!='VERIFIED_EXACT_PUBLIC_BODY':unavailable.append({'reference':url,'reason':'Exact reviewed public body unavailable'});continue
   b=(a.body_root/repo.replace('/','--')/pin/parts).read_bytes();blob=source['entry']['sha'];license_status=source['license_status']
   assert len(b)==source['bytes'] and hashlib.sha256(b).hexdigest()==source['sha256']
  elif repo=='Sodelin/Research-Commons' and ref['coverage'] in ('repository_artifact_outside_selected_roots','selected_tree_version_or_representation_gap','referenced_exact_version_full_text') and (ref.get('original_git_blob') or ref.get('git_blob')):
   result=subprocess.run(['git','-C',str(a.repo),'show',pin+':'+path],capture_output=True)
   assert result.returncode==0, 'Pinned Commons body disappeared'
   b=result.stdout;blob=ref.get('original_git_blob') or ref['git_blob'];license_status='Research Commons own-research reference intake; consult the original repository license and source attribution.'
  elif repo!='Sodelin/Research-Commons' and ref['coverage']=='external_repository_body_unbound':
   unavailable.append({'reference':url,'reason':'Other-owner source remains link-only; no body intake authorized by this manifest'});continue
  else:continue
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==blob, 'Git blob mismatch'
  assert len(b)<=16*1024*1024 and b'\0' not in b, 'Non-text or oversized input'
  body=b.decode('utf-8',errors='strict')
  # The intake is intentionally scientific public text only. Do not copy host
  # coordinates, authentication strings or private artifact IDs into a corpus.
  if re.search(r'(?:gh[pousr]_[A-Za-z0-9]{20,}|AKIA[0-9A-Z]{16}|sk-[A-Za-z0-9]{30,}|libfile_[0-9a-f]{20,}|file_00000000[0-9a-f]+)',body):
   unavailable.append({'reference':url,'reason':'Public-source privacy marker requires review; body excluded'});continue
  documents.append({'url':f'https://github.com/{repo}/blob/{pin}/{path}','repository':repo,'commit':pin,'source_paths':[path],'title':repo+' / '+path,'git_blob':blob,'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'body':body,'bindings':[{'claim_id':v['record_id'],'role':'canonical_reference_only','label':v['metadata_path']} for v in ref['bindings'] if (v.get('record_id') or '').startswith('CB-')],'evidence_role':ROLE,'license_status':license_status})
 unique={}
 for d in documents:
  if d['url'] in unique:
   old=unique[d['url']];assert old['sha256']==d['sha256']
   for binding in d['bindings']:
    if binding not in old['bindings']:old['bindings'].append(binding)
  else:unique[d['url']]=d
 documents=list(unique.values())
 result={'schema':1,'view':'exact_canonical_reference_bodies','canonical_reference_source_commit':refs['tree_source_commit'],'reference_inventory_sha256':hashlib.sha256(a.references.read_bytes()).hexdigest(),'verified_inputs_sha256':hashlib.sha256(a.verified_inputs.read_bytes()).hexdigest(),'documents':documents,'unavailable':unavailable,'coverage':dict(collections.Counter(d['repository'] for d in documents)),'limitation':'Exact cited versions only, not complete linked repositories or every result. Bodies carry source evidence, not canonical claim status, reviewer acceptance, execution or a new redistribution license. Other-owner references remain link-only. Generated local corpus is not a hosted deployment.'}
 a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n');print(json.dumps({'documents':len(documents),'unavailable':len(unavailable),'repositories':result['coverage']}))

if __name__=='__main__':main()
