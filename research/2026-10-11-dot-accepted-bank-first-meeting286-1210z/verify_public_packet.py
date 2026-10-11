from pathlib import Path
import json,hashlib,gzip
P=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
for r in json.loads((P/'MANIFEST.json').read_text())['files']:
 b=(P/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+bytes([0])+b).hexdigest()==r['git_blob']
t=json.loads((P/'DEPENDENCY-GRAPH.json').read_text())['targets']['candidate/g4-first-meeting'];assert len(t['modules'])==286;seen=set()
for n in t['order']:
 r=t['modules'][n];assert sha((P/'source-store'/(r['sha256']+'.lean')).read_bytes())==r['sha256'];assert all(i not in t['modules'] or i in seen for i in r['imports']);seen.add(n)
x=json.loads((P/'AUDIT-TRANSPORT.json').read_text());z=(P/'evidence/AUDIT-RESULT.json.gz').read_bytes();assert sha(z)==x['gzip_sha256'];b=gzip.decompress(z);assert len(b)==x['raw_bytes'] and sha(b)==x['raw_sha256'];a=json.loads(b);assert a['declaration_count']==6122 and a['theorem_declaration_count']==4197;assert not a['owned_axioms'] and not a['nonstandard_axiom_rows'] and not a['missing_modules'];assert len(a['selected_modules'])==286
print('PASS exact public packet, selected286 graph and complete audit; no compiler invoked.')
