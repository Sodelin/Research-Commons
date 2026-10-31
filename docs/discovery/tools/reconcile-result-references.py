#!/usr/bin/env python3
"""Account for canonical references beyond selected tree roots without claiming ingestion."""
import argparse,collections,hashlib,json,pathlib,re,subprocess,urllib.parse
p=argparse.ArgumentParser();p.add_argument('--repo',type=pathlib.Path,default=pathlib.Path('.'));p.add_argument('--manifest',type=pathlib.Path,required=True);p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--reference-bodies',type=pathlib.Path);a=p.parse_args();m=json.loads(a.manifest.read_bytes());rows={r['path']:r for r in m['inventory']};refs={};metadata=[]
files=['docs/claims.json','docs/programmes.json','docs/dissemination.json','docs/discovery/dist/reading-joins.json']
for name in files:
 result=subprocess.run(['git','-C',str(a.repo),'show',m['commit']+':'+name],capture_output=True)
 if result.returncode:continue
 data=result.stdout;metadata.append({'path':name,'sha256':hashlib.sha256(data).hexdigest()})
 def walk(x,owner=None):
  if isinstance(x,dict):
   owner=x.get('id',owner)
   for y in x.values():walk(y,owner)
  elif isinstance(x,list):
   for y in x:walk(y,owner)
  elif isinstance(x,str):
   urls=re.findall(r'https?://[^\s<>"\]\)]+',x)
   if re.fullmatch(r'(?:research|docs|packages|handoffs|communications)/[^\s]+',x):urls.append(x)
   for url in urls:
    binding={'metadata_path':name,'record_id':owner}
    if binding not in refs.setdefault(url,[]):refs[url].append(binding)
 walk(json.loads(data))
corpus=subprocess.run(['git','-C',str(a.repo),'show',m['commit']+':docs/discovery/dist/source-corpus.json'],capture_output=True);bundled={}
if corpus.returncode==0:
 for d in json.loads(corpus.stdout)['documents']:
  body=d['body'].encode();assert hashlib.sha256(body).hexdigest()==d['sha256'];assert hashlib.sha1(f'blob {len(body)}\0'.encode()+body).hexdigest()==d['git_blob'];bundled[d['url']]=d
reference_bodies={}
if a.reference_bodies:
 supplement=json.loads(a.reference_bodies.read_bytes());assert supplement['schema']==1 and supplement['view']=='exact_canonical_reference_bodies'
 for d in supplement['documents']:
  b=d['body'].encode();assert hashlib.sha256(b).hexdigest()==d['sha256'];assert hashlib.sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==d['git_blob'];reference_bodies[d['url']]=d
records=[]
for url,bindings in sorted(refs.items()):
 record={'reference':url,'bindings':bindings};parsed=urllib.parse.urlsplit(url);assert not parsed.username and not parsed.password,'Credential-bearing reference refused';normalized=urllib.parse.urlunsplit((parsed.scheme,parsed.netloc,parsed.path,'',''));match=re.fullmatch(r'https://github.com/([^/]+/[^/]+)/(blob|tree)/([^/]+)/(.+)',normalized)
 if normalized in reference_bodies:
  d=reference_bodies[normalized];record.update(coverage='referenced_exact_version_full_text',repository=d['repository'],source_revision=d['commit'],source_path=d['source_paths'][0],body_sha256=d['sha256'],git_blob=d['git_blob'],license_status=d['license_status'],source_view='--research-results MANIFEST --reference-bodies CORPUS; generated local input, no hosted deployment inferred')
 elif normalized in bundled:record.update(coverage='bundled_selected_full_text',body_sha256=bundled[normalized]['sha256'],git_blob=bundled[normalized]['git_blob'],source_view='existing --sources corpus; separately pinned historical snapshot')
 elif match:
  repo,kind,pin,path=match.groups();path=urllib.parse.unquote(path);record.update(repository=repo,source_revision=pin,source_path=path)
  if kind=='tree':record['coverage']='directory_reference_only_requires_inventory'
  elif not re.fullmatch('[a-f0-9]{40}',pin):record['coverage']='unversioned_reference_no_immutable_body_binding'
  elif repo!='Sodelin/Research-Commons':record['coverage']='external_repository_body_unbound'
  else:
   result=subprocess.run(['git','-C',str(a.repo),'rev-parse','--verify',pin+':'+path],capture_output=True,text=True)
   original=result.stdout.strip() if result.returncode==0 else None;record['original_git_blob']=original
   if original is None:record.update(coverage='repository_artifact_missing_at_pinned_ref',diagnostic='git rev-parse could not resolve the exact cited revision:path; no replacement inferred')
   elif path in rows and original==rows[path]['git_blob'] and rows[path]['coverage']=='full_text':record.update(coverage='selected_tree_full_text_same_immutable_blob',body_sha256=rows[path]['sha256'],indexed_url=rows[path]['document_url'])
   elif path in rows:record.update(coverage='selected_tree_version_or_representation_gap',inventory_coverage=rows[path]['coverage'])
   else:record['coverage']='repository_artifact_outside_selected_roots'
 elif not urllib.parse.urlsplit(url).scheme:
  record.update(source_path=url,coverage='relative_artifact_outside_selected_roots' if url not in rows else rows[url]['coverage']);
  if url in rows:record.update(git_blob=rows[url]['git_blob'],body_sha256=rows[url].get('sha256'))
 else:record['coverage']='external_reference_url_only'
 records.append(record)
result={'schema':1,'tree_source_commit':m['commit'],'metadata_inputs':metadata,'selected_roots':m['roots'],'reference_count':len(records),'coverage_counts':dict(collections.Counter(r['coverage'] for r in records)),'records':records,'limitation':'Explicit canonical reference accounting; referenced_exact_version_full_text requires the separately hash-verified local body supplement. No scientific acceptance or hosted deployment inferred. The selected tree is not every user result: docs/packages, other commits, linked repositories and external resources have separate gaps. No private task data or unpublished handoffs are ingested.'};a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'references':len(records),'coverage':result['coverage_counts']}))
