#!/usr/bin/env python3
"""Derive a bounded public authored-document inventory, never a status register.

GitHub GraphQL batches exact tree objects to avoid ~1000 separate REST calls.
Only publication metadata is projected; no source body/runtime/credentials read.
"""
import collections,json,pathlib,subprocess
from urllib.parse import quote
ROOT=pathlib.Path(__file__).resolve().parents[1]
REPO='Sodelin/Research-Commons'
SELECT=('research','docs','notes','reports','applications','brainstorms')
EXCLUDE={'vendor','upstream','node_modules','target','dist','build','.git','.lake','Mathlib','Batteries','Aesop','Qq','ProofWidgets','Lean','Init','Std','third-party'}
def api(path):return json.loads(subprocess.check_output(['gh','api','repos/'+REPO+path],timeout=45))
def trees(expressions):
 fields=' '.join('t'+str(i)+':object(expression:'+json.dumps(e)+'){... on Tree{entries{name type oid mode object{... on Blob{byteSize}}}}}' for i,e in enumerate(expressions))
 query='query{repository(owner:"Sodelin",name:"Research-Commons"){'+fields+'}}'
 result=json.loads(subprocess.check_output(['gh','api','graphql','-f','query='+query],timeout=45))
 if result.get('errors'):raise RuntimeError('GraphQL errors: previous inventory preserved')
 repo=result['data']['repository']
 values=[repo['t'+str(i)] for i in range(len(expressions))]
 if any(v is None or 'entries'not in v for v in values):raise RuntimeError('Missing tree: previous inventory preserved')
 return [v['entries'] for v in values]
def collect():
 commit=api('/git/ref/heads/main')['object']['sha']
 root=api('/git/trees/'+commit)
 if root.get('truncated'):raise RuntimeError('Root tree truncated')
 pending=collections.deque([(e['path'],e['sha']) for e in root['tree'] if e['type']=='tree'and e['path']in SELECT])
 entries=[];excluded=[];tree_count=0;seen=0
 for e in root['tree']:
  if e['type']=='blob'and e.get('mode')=='100644'and e['path'].lower().endswith('.md'):
   entries.append({'path':e['path'],'git_blob':e['sha'],'bytes':e.get('size')})
 while pending:
  batch=[pending.popleft() for _ in range(min(25,len(pending)))]
  result=trees([sha for path,sha in batch]);tree_count+=len(batch)
  for (prefix,_),children in zip(batch,result):
   for e in children:
    path=prefix+'/'+e['name'];seen+=1
    if seen>150000 or tree_count>10000:raise RuntimeError('Inventory bound exceeded: previous source preserved')
    if e['type']=='tree':
     if e['name']in EXCLUDE or path=='docs/discovery':excluded.append(path)
     else:pending.append((path,e['oid']))
    elif e['type']=='blob'and e['mode']==33188 and path.lower().endswith('.md'):
     entries.append({'path':path,'git_blob':e['oid'],'bytes':(e.get('object')or{}).get('byteSize')})
  print('Exact trees inspected: '+str(tree_count)+'; documents: '+str(len(entries)),flush=True)
 entries.sort(key=lambda e:e['path'])
 for e in entries:
  e['url']='https://github.com/'+REPO+'/blob/'+commit+'/'+quote(e['path'],safe='/')
  e['group']='/'.join(e['path'].split('/')[:2]) if e['path'].startswith('research/') else e['path'].split('/')[0]
  e['title']=e['path'].replace('/',' · ').replace('-',' ').replace('_',' ')
 return {'schema':1,'repository':REPO,'commit':commit,'coverage':{'kind':'public source path inventory','roots':list(SELECT),'documents':len(entries),'trees_inspected':tree_count,'entries_inspected':seen,'excluded_subtrees':sorted(excluded),'limitations':'Paths and Git identities only, not full-text body search, scientific acceptance, all Git history, private tasks or every repository. No result/status is inferred from a filename.'},'documents':entries}
if __name__=='__main__':
 result=collect();target=ROOT/'dist/archive-catalog.json';pending=target.with_suffix('.json.pending')
 pending.write_text(json.dumps(result,separators=(',',':')));pending.replace(target)
 print(json.dumps({'documents':len(result['documents']),'trees':result['coverage']['trees_inspected'],'commit':result['commit']}))
