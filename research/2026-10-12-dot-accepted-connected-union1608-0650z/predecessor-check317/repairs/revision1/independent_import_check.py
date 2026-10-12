from pathlib import Path
import json,hashlib,re
P=Path(__file__).parent;B=Path('LOCAL_EVIDENCE/connected-union1607-20261012-0558z');H=lambda b:hashlib.sha256(b).hexdigest();R=lambda p:json.loads(p.read_bytes());ledger=R(P/'DEPENDENCY-LEDGER.json');g=R(B/'DEPENDENCY-GRAPH.json')['targets']['current/connected']['modules'];source=P/'G4ActualLegalPanelComb.lean'
assert H(source.read_bytes())==ledger['source_sha256']=='0c66f76af642dcf7b91e84c040015a34ce676be1c3c28e29bd209c310c3d9677'
def imports(s):
 out=[];i=dep=0
 while i<len(s):
  if s[i:i+2]=='/-':dep+=1;i+=2
  elif dep and s[i:i+2]=='-/':dep-=1;i+=2
  elif not dep and s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
  elif not dep and s[i:i+2]=='--':
   end=s.find('\n',i);i=len(s) if end<0 else end
  else:
   if not dep:out.append(s[i])
   i+=1
 assert dep==0
 return [n for line in re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+([^\n]+)', ''.join(out),re.M) for n in line.split() if n!='all']

assert imports(source.read_text())==ledger['imports'];seen={}
for e in ledger['providers']:
 n=e['module'];assert (e['sha256'],e['imports'])==(g[n]['sha256'],g[n]['imports']);b=(B/'source-store'/(e['sha256']+'.lean')).read_bytes();assert H(b)==e['sha256'];assert imports(b.decode())==e['imports'],n;seen[n]=e
need=set()
def visit(n):
 if n not in g or n in need:return
 need.add(n)
 for q in g[n]['imports']:visit(q)
for n in ledger['imports']:visit(n)
assert set(seen)==need and len(need)==316
r={'status':'EXACT_STATIC_SOURCE_IMPORT_CLOSURE_PASS','source_sha256':H(source.read_bytes()),'ledger_sha256':H((P/'DEPENDENCY-LEDGER.json').read_bytes()),'accepted_graph_sha256':H((B/'DEPENDENCY-GRAPH.json').read_bytes()),'providers_rehashed':316,'direct_imports':ledger['imports'],'compiler_invoked':False};(P/'INDEPENDENT-IMPORT-CHECK.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
