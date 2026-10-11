"""Compare a freshly reproduced terminal run with the published exact mathematical audit."""
from pathlib import Path
import gzip,json,hashlib
P=Path(__file__).resolve().parent
read=lambda p:json.loads(p.read_bytes())
g=read(P/'DEPENDENCY-GRAPH.json');f=read(P/'.build/LATEST-RUN.json')
assert f['status']=='PASS_ALL_REQUESTED_TARGETS' and f['trust_level']==0 and f['kernel_checking']
assert f['graph_sha256']==hashlib.sha256((P/'DEPENDENCY-GRAPH.json').read_bytes()).hexdigest()
for m,e in g['targets']['current/connected']['modules'].items():assert hashlib.sha256((P/'source-store'/(e['sha256']+'.lean')).read_bytes()).hexdigest()==e['sha256'],m
r=read(Path(f['run'])/'targets/current_connected/RESULT.json');assert r['status']=='PASS'
a=read(Path(r['audit_receipt']['audit_output']));raw=gzip.decompress((P/'evidence/AUDIT-RESULT.json.gz').read_bytes() if (P/'evidence/AUDIT-RESULT.json.gz').exists() else b''.join((P/x['path']).read_bytes() for x in read(P/'AUDIT-TRANSPORT.json')['parts']));assert hashlib.sha256(raw).hexdigest()=='ee29bc1196c22fb27dd024e8593b0208aba5f4195edbf4895871235ee6e42e53';expected=json.loads(raw)
assert not a['owned_axioms'] and not a['nonstandard_axiom_rows'] and not a['missing_modules']
assert a['selected_modules']==expected['selected_modules']
assert {x['name']:x for x in a['declarations']}=={x['name']:x for x in expected['declarations']}
assert a['declaration_count']==101705 and a['theorem_declaration_count']==92153
print('PASS: exact1568 source/declaration union, fresh terminal aggregate/audit')
