"""Read-only source/import authentication; never invokes Lean or a compiler."""
import argparse, hashlib, json, re
from pathlib import Path
p=argparse.ArgumentParser(); p.add_argument('--packet',type=Path,required=True); p.add_argument('--accepted',type=Path,required=True); p.add_argument('--coefficient',type=Path,required=True); p.add_argument('--mathlib',type=Path,required=True); a=p.parse_args()
h=lambda b:hashlib.sha256(b).hexdigest()
def imports(txt):
    # Lexically remove nested comments and quoted strings before reading imports.
    out=[]; i=0; depth=0; quoted=False
    while i<len(txt):
        pair=txt[i:i+2]; ch=txt[i]
        if depth:
            if pair=='/-': depth+=1; i+=2; continue
            if pair=='-/': depth-=1; i+=2; continue
            out.append('\n' if ch=='\n' else ' '); i+=1; continue
        if quoted:
            if ch=='\\': out.extend('  '); i+=2; continue
            if ch=='"': quoted=False
            out.append('\n' if ch=='\n' else ' '); i+=1; continue
        if pair=='/-': depth=1; i+=2; continue
        if pair=='--':
            end=txt.find('\n',i); i=len(txt) if end<0 else end; continue
        if ch=='"': quoted=True; out.append(' '); i+=1; continue
        out.append(ch); i+=1
    assert depth==0 and not quoted
    return re.findall(r'^\s*import\s+(\S+)', ''.join(out), re.M)
lb=(a.packet/'SOURCE-IMPORT-LEDGER.json').read_bytes(); ledger=json.loads(lb)
gb=(a.accepted/'DEPENDENCY-GRAPH.json').read_bytes(); graph=json.loads(gb)['targets']['current/connected']['modules']
assert h(gb)==ledger['accepted_graph_sha256']
drafts={'G4SpecifiedCombSelectedObservation':a.packet/'G4SpecifiedCombSelectedObservation.lean','G4SpecifiedCombEvent':a.coefficient}
rows=[]
for n,d in ledger['modules'].items():
    if n in drafts: f=drafts[n]
    else:
        assert n in graph
        assert d['sha256']==graph[n]['sha256'] and d['imports']==graph[n]['imports']
        f=a.accepted/'source-store'/(d['sha256']+'.lean')
    b=f.read_bytes()
    assert h(b)==d['sha256'],n
    assert imports(b.decode())==d['imports'],n
    rows.append({'module':n,'sha256':h(b),'bytes':len(b),'git_blob':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()})
seen=set(); external=set()
def visit(n):
    if n in seen: return
    if n not in ledger['modules']: external.add(n); return
    seen.add(n)
    for child in ledger['modules'][n]['imports']: visit(child)
visit('G4SpecifiedCombSelectedObservation')
assert seen==set(ledger['modules'])
assert external==set(ledger['external_imports'])
assert len(rows)==183 and len(graph)==1591 and len(rows)-len(drafts)==181
mathfiles={}
for rel in ['Mathlib/Probability/ProbabilityMassFunction/Basic.lean','Mathlib/Probability/ProbabilityMassFunction/Constructions.lean','Mathlib/Data/Finset/Insert.lean']:
    b=(a.mathlib/rel).read_bytes(); mathfiles[rel]={'sha256':h(b),'bytes':len(b)}
text=drafts['G4SpecifiedCombSelectedObservation'].read_text()
heads=re.findall(r'^(?:lemma|theorem)\s+(\w+)',text,re.M)
assert heads==['supported_completed_forest_at_B','actual_completed_forest_singleton_mass','selected_completed_forest_law','actual_selected_specified_comb_probability']
assert not re.search(r'\b(sorry|admit|native_decide)\b',text)
result={'status':'PASS_READ_ONLY_SOURCE_IMPORT_AUTHENTICATION_NOT_ELABORATION','source_sha256':h(drafts['G4SpecifiedCombSelectedObservation'].read_bytes()),'ledger_sha256':h(lb),'accepted_commit':ledger['accepted_commit'],'accepted_graph_sha256':h(gb),'accepted_prerequisites':181,'uncompiled_sources':2,'closure_modules':183,'external_imports':len(external),'declaration_heads':heads,'mathlib_commit_checked_separately':'0df444a360eaa60ab8c11dca51a86af692955474','direct_mathlib_files':mathfiles,'sources':sorted(rows,key=lambda r:r['module']),'compiler_invoked':False,'accepted_sources_modified':False}
(a.packet/'INDEPENDENT-STATIC-CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['sources','direct_mathlib_files']},indent=2))
