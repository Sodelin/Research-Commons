"""Read-only byte/source/audit verification of the distributed evidence packet.
This does not launch Lean or replace the independent kernel/native review.
"""
from pathlib import Path
import hashlib,json,gzip
P=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
manifest=json.loads((P/'MANIFEST.json').read_bytes())
for r in manifest['files']:
 b=(P/r['path']).read_bytes();assert len(b)==r['bytes'] and H(b)==r['sha256'],r['path']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+bytes([0])+b).hexdigest()==r['git_blob'],r['path']
g=json.loads((P/'DEPENDENCY-GRAPH.json').read_bytes());a=json.loads((P/'ACCEPTANCE.json').read_bytes());assert H((P/'DEPENDENCY-GRAPH.json').read_bytes())==a['graph_sha256']
for t in g['targets'].values():
 for n,e in t['modules'].items():assert H((P/'source-store'/(e['sha256']+'.lean')).read_bytes())==e['sha256'],n
assert len(g['targets']['current/connected']['modules'])==1585
tr=json.loads((P/'AUDIT-TRANSPORT.json').read_bytes());parts=[]
for e in tr['parts']:
 b=(P/e['path']).read_bytes();assert len(b)==e['bytes'] and H(b)==e['sha256'];parts.append(b)
z=b''.join(parts);assert H(z)==tr['gzip_sha256'];raw=gzip.decompress(z);assert H(raw)==tr['raw_sha256']==a['audit_sha256'];d=json.loads(raw)
assert d['declaration_count']==102014 and d['theorem_declaration_count']==92386
assert not d['owned_axioms'] and not d['nonstandard_axiom_rows'] and not d['missing_modules']
assert set(d['selected_modules'])==set(g['targets']['current/connected']['modules'])
print('PASS: distributed bytes, all source targets and exact complete mathematical audit; no compiler replay claimed')
