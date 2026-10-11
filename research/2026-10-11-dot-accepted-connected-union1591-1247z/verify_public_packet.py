"""Verify public payload identities and complete mathematical audit; invokes no compiler."""
from pathlib import Path
import json,hashlib,gzip
P=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
for r in json.loads((P/'MANIFEST.json').read_text())['files']:
 b=(P/r['path']).read_bytes();assert len(b)==r['bytes'] and sha(b)==r['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+bytes([0])+b).hexdigest()==r['git_blob']
g=json.loads((P/'DEPENDENCY-GRAPH.json').read_text());t=g['targets']['current/connected'];assert len(t['modules'])==1591;assert 'G7OriginalPopulationFixture' not in t['modules'];seen=set()
for n in t['order']:
 r=t['modules'][n];b=(P/'source-store'/(r['sha256']+'.lean')).read_bytes();assert sha(b)==r['sha256'];assert all(i not in t['modules'] or i in seen for i in r['imports']);seen.add(n)
x=json.loads((P/'AUDIT-TRANSPORT.json').read_text());z=b''.join((P/r['path']).read_bytes() for r in x['parts']);assert sha(z)==x['gzip_sha256'];b=gzip.decompress(z);assert len(b)==x['raw_bytes'] and sha(b)==x['raw_sha256'];a=json.loads(b);assert a['declaration_count']==102163 and a['theorem_declaration_count']==92503;assert not a['owned_axioms'] and not a['nonstandard_axiom_rows'] and not a['missing_modules'];assert len(a['selected_modules'])==1591
print('PASS: public packet identities, selected1591 graph and exact complete audit; no fresh compiler replay claimed.')
