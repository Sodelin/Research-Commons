"""Public source/config/audit evidence verifier. No compiler, network or native payload replay."""
from pathlib import Path
import gzip,hashlib,json,re
P=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def read(n):
 q=Path(n);require(not q.is_absolute() and '..' not in q.parts,'unsafe manifest path');p=P/q
 require(p.is_file() and not p.is_symlink(),'missing/unsafe file: '+n);return p.read_bytes()
def load(n):return json.loads(read(n))
def manifest(root=''):
 m=load(root+'MANIFEST.json')
 for r in m['files']:
  b=read(root+r['path']);require(len(b)==r['bytes'] and sha(b)==r['sha256'],'file hash: '+root+r['path'])
  require(hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r.get('git_blob',r.get('git_blob_sha1',r.get('git_blob_sha'))),'Git blob: '+r['path'])
 return m
m=manifest();manifest('predecessor-check310/')
g=load('DEPENDENCY-GRAPH.json');t=g['targets']['current/connected'];require(len(t['modules'])==1598,'module count');require('G7OriginalPopulationFixture' not in t['modules'],'fixture isolation')
allsha=set()
for target in g['targets'].values():
 for n,r in target['modules'].items():
  h=r['sha256'];require(sha(read('source-store/'+h+'.lean'))==h,'source '+n);allsha.add(h)
require(len(allsha)==1599,'complete source store')
seen=set()
for n in t['order']:
 require(n not in seen and n in t['modules'],'order identity');require(all(i not in t['modules'] or i in seen for i in t['modules'][n]['imports']),'import order '+n);seen.add(n)
require(seen==set(t['modules']),'complete module order')
prep=load('PREPARATION.json');require(sha(read('DEPENDENCY-GRAPH.json'))==prep['graph_sha256'],'prepared graph')
for n,h in prep['scripts'].items():require(sha(read('scripts/'+n))==h,'exact executable script '+n)
def restore(x):
 chunks=[]
 for r in x['parts']:
  b=read(r['path']);require(len(b)==r['bytes'] and sha(b)==r['sha256'],'part identity');chunks.append(b)
 z=b''.join(chunks);require(len(z)==x['gzip_bytes'] and sha(z)==x['gzip_sha256'],'compressed stream identity');b=gzip.decompress(z);require(len(b)==x['raw_bytes'] and sha(b)==x['raw_sha256'],'recovered bytes');return b
raw=restore(load('AUDIT-TRANSPORT.json'));a=json.loads(raw)
require(a['declaration_count']==102407 and a['theorem_declaration_count']==92697,'audit counts');require(not a['owned_axioms'] and not a['nonstandard_axiom_rows'] and not a['missing_modules'],'audit exceptions');require(len(a['selected_modules'])==1598,'audit modules')
for r in load('PUBLIC-PROJECTIONS.json')['entries']:
 b=restore(r['transport']) if 'transport' in r else read(r['path']);require(sha(b)==r['public_sha256'] and len(b)==r['public_bytes'],'projection public hash')
 if r['status']=='EXACT_BYTES':require(r['public_sha256']==r['raw_sha256'],'exact projection')
acc=load('ACCEPTANCE.json');require(acc['authenticated_reused_components']==1598 and acc['fresh_mathematical_components_in_terminal_run']==0,'freshness scope');require(acc['raw_audit_sha256']==sha(raw),'audit acceptance')
require(sha(read('independent/INDEPENDENT-FINAL-REVIEW.md'))==acc['independent_agent_review_raw_sha256'],'independent review')
x=load('independent/TERMINAL-EVIDENCE-CHECK.json');require(x['retained_prior_names']==102370 and not x['changed_prior_records'],'reported inherited comparison');require(len(x['new_records'])==37,'new-record count')
records=a.get('declarations',a.get('declaration_records'))
require(records is not None,'audit records schema')
rows={r['name']:r for r in records} if isinstance(records,list) else records
nr=x['new_records']; nr=nr.values() if isinstance(nr,dict) else nr
for r in nr:require(rows[r['name']]==r,'new record exact equality '+r['name'])
print('PASS: public manifest, 1599 source bodies, selected1598 graph, exact build scripts, predecessor evidence, operational transports and complete audit. No compiler or native-payload replay claimed.')
