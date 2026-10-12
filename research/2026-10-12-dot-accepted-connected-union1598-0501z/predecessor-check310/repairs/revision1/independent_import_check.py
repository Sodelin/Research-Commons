from pathlib import Path
import json,hashlib,re
P=Path(__file__).parent;B=Path('LOCAL_EVIDENCE/connected-union1597-20261012-0431z');H=lambda b:hashlib.sha256(b).hexdigest();rd=lambda p:json.loads(p.read_bytes());l=rd(P/'DEPENDENCY-LEDGER.json');g=rd(B/'DEPENDENCY-GRAPH.json')['targets']['current/connected']['modules']
assert l['source_sha256']=='92486cb1efd96e9d538b52de511840b852725a2ee1d5c4fa4e00ce717e41f3b1' and H((P/'G4ActualObservableBankCertificate.lean').read_bytes())==l['source_sha256']
def imports(b):
 s=b.decode();s=re.sub(r'--[^\n]*','',s)
 # All nested Lean block comments are erased before literal import parsing.
 out=[];i=depth=0
 while i<len(s):
  if s[i:i+2]=='/-':depth+=1;i+=2
  elif depth and s[i:i+2]=='-/':depth-=1;i+=2
  else:
   if depth==0:out.append(s[i])
   i+=1
 assert depth==0
 return [m for x in re.findall(r'^\s*import\s+([^\n]+)', ''.join(out),re.M) for m in x.split()]
assert imports((P/'G4ActualObservableBankCertificate.lean').read_bytes())==l['imports'];seen={}
for e in l['providers']:
 n=e['module'];assert (e['sha256'],e['imports'])==(g[n]['sha256'],g[n]['imports']);b=(B/'source-store'/(e['sha256']+'.lean')).read_bytes();assert H(b)==e['sha256'];assert imports(b)==e['imports'],n;seen[n]=e
need=set()
def visit(n):
 if n not in g or n in need:return
 need.add(n)
 for q in g[n]['imports']:visit(q)
for n in l['imports']:visit(n)
assert set(seen)==need and len(need)==309
r={'status':'EXACT_SOURCE_IMPORT_CLOSURE_PASS_STATIC_ONLY','source_sha256':l['source_sha256'],'ledger_sha256':H((P/'DEPENDENCY-LEDGER.json').read_bytes()),'accepted_graph_sha256':H((B/'DEPENDENCY-GRAPH.json').read_bytes()),'providers_rehashed':309,'literal_direct_imports':l['imports'],'all_declared_recursive_imports_match':True,'compiler_invoked':False};(P/'INDEPENDENT-IMPORT-CHECK.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r,indent=2))
