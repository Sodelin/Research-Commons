"""Freeze complete named text evidence for one source-only Git checkpoint."""
import pathlib,hashlib,json,sys
WF=pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
WN=pathlib.Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
D=pathlib.Path(__file__).resolve().parent
B=WF/'metadata/git-evidence-publication'
P='research/2026-10-10-codex-lean-rust-parity'
prefix=P+'/quality/evidence/git-preserved/source-observer-integration-20261011T0419Z'
def sha(b):return hashlib.sha256(b).hexdigest()
rows=[]
def add(p,target):
    assert p.is_file() and not p.is_symlink()
    b=p.read_bytes();b.decode('utf-8');assert not b.startswith(b'\x7fELF')
    rows.append({'source_path':str(p),'git_tree_path':target,'bytes':len(b),'sha256':sha(b)})
def evidence(p):
    if p.is_relative_to(WF):target=prefix+'/WF/'+str(p.relative_to(WF))
    else:assert p.is_relative_to(WN);target=prefix+'/WN/'+str(p.relative_to(WN))
    add(p,target)
def group(p,exclude=()):
    assert p.is_dir()
    for f in sorted(p.rglob('*')):
        if f.is_file():
            if f.name in exclude:continue
            assert f.suffix not in ('.gz','.rlib','.olean','.ilean')
            evidence(f)
for p,exclude in [
(WF/'metadata/selected-prefix-erased-observer-sourceonly-20261011T0254Z',()),
(WF/'metadata/erased-selected-observer-independent-qc-20261011T032452.501810Z-lean-reuse-successor',()),
(WF/'metadata/erased-selected-observer-validation-sourceonly-20261011T0327Z',('erased-selected-observer-tests',)),
(WF/'metadata/source-only-observer-execution-guard-20261011T0338Z',()),
(WF/'metadata/erased-observer-harness-independent-qc-20261011T034947.152719Z-lean-reuse-successor',()),
(WF/'design-qc/erased-observer-harness-guard-20261011T0350Z-solver_design_recovery',()),
(WF/'metadata/erased-observer-actual-saved-qc-20261011T035853.923228Z-lean-reuse-successor',()),
(WF/'metadata/g4-calibrated-meeting-source-bridge-review-20261011T034109.213385Z',()),
(WF/'metadata/g4-literal-last-child-exit-bridge-draft-20261011T040345.699402Z',()),
(WF/'metadata/inverse-bridge-structural-construction-20261011T031257.933549Z-lean-reuse-successor',()),
(WN/'metadata/direct-owned-audit-gzip-1575-feasibility-20261011T031815Z',('measure_sourceonly_v1.py.gz','measure_sourceonly_v2.py.gz')),
(B/'final-gate-review-correction',()),
(B/'core-remote-readback-20261011T0344Z',()),
(WF/'design-qc/observer-text-publication-20261011T0356Z-solver_design_recovery',()),
]:group(p,exclude)
for f in [
WF/'metadata/G4-LITERAL-LAST-CHILD-EXIT-INDEPENDENT-CRITIQUE-20261011T0410Z.json',
WF/'metadata/INVERSE-BRIDGE-STRUCTURAL-CRITIQUE-20261011T0321Z.md',
WF/'metadata/INVERSE-BRIDGE-STRUCTURAL-CRITIQUE-20261011T0321Z.json',
B/'DIRECT-GZIP-FEASIBILITY-EARLIER-SOURCE-VERSIONS-LOSSLESS.json',
B/'FINAL-REMAINING-APPLY.stdout',B/'FINAL-REMAINING-APPLY.stderr',
B/'FINAL-CORE-CHECKPOINT-COMMIT-READBACK.json',
]:evidence(f)
# Include every source version, exact own correction and native prelaunch evidence.
for f in sorted(D.iterdir()):
    if f.is_file():
        assert f.name not in ('INPUTS.json','FUNDING-GATE.json','ACTUAL-PUBLICATION.json')
        evidence(f)
# The fresh Commons capture retains all original note bodies at canonical paths.
peer=WF/'metadata/peer-main-new-20261011T0415Z'
j=json.loads((peer/'FULL-API-CAPTURE.json').read_bytes())
assert j['ref']=='73a3175b8667eebf0b9e93793cf3d9d3b4593d0b' and len(j['rows'])==7
for r in j['rows']:
    f=pathlib.Path(r['source_path']);b=f.read_bytes()
    assert sha(b)==r['sha256'] and len(b)==r['bytes']
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==r['git_blob']
    add(f,r['git_tree_path'])
evidence(peer/'FULL-API-CAPTURE.json')
# Separate local capture correction is retained; canonical note is the exact body.
add(B/'core-remote-readback-20261011T0344Z/COMMONS-HANDOFF-EXACT-FULLTEXT.md','communications/2026-10-11-codex-common141-accepted-five-source1575-handoff-0340z.md')
acceptance=D/'PRIVATE-ERASED-SELECTED-OBSERVER-FIVE-TEST-ACCEPTANCE-20261011T0404Z.json'
assert sha(acceptance.read_bytes())=='fad721307270635563db8c52dc427b2c296f20938d83be759ffb52b1cf144f79'
add(acceptance,P+'/quality/'+acceptance.name)
state=D/'INTEGRATION-STATE-20261011T0419Z.md'
add(state,P+'/design/'+state.name)
# Additional independent G3 review and next G4 proof target are complete frozen texts.
assert len(sys.argv)==3
for arg in sys.argv[1:]:
    f=pathlib.Path(arg);assert f.is_relative_to(WF)
    evidence(f)
assert len({r['git_tree_path'] for r in rows})==len(rows)
assert len(rows)+4<=256
source=D/'publish_reviewed_text_v3.py'
assert sha(source.read_bytes())=='6c9fd8cd57d8cc8400804e104c652857275ab66c1559f98a68e8dbbff71da15c'
m={'schema':'full_source_observer_integration_manifest_v1','publisher_sha256':sha(source.read_bytes()),'base_head':'4862b9618ca422da4ad5381b5dec0a3fcac56e76','base_tree':'145eefb4baaec4eafca16622ed9fdfb538313922','prefix':prefix,'scope':'Full original UTF-8 sources, run evidence and reviews; excludes compiled binaries and caches. Full selected body preservation is not kernel/master acceptance. Gate, final independent publication QC and actual receipt are separately added by the publisher.','excluded_binary_immutable_native_paths':[str(WF/'metadata/erased-selected-observer-validation-sourceonly-20261011T0327Z/execution-1/erased-selected-observer-tests')],'earlier_gzip_sources_full_lossless_wrapper':str(B/'DIRECT-GZIP-FEASIBILITY-EARLIER-SOURCE-VERSIONS-LOSSLESS.json'),'newest_reviewed_main_ref':j['ref'],'files':rows}
p=D/'INPUTS.json';assert not p.exists();b=(json.dumps(m,indent=2)+'\n').encode();p.write_bytes(b)
print(json.dumps({'status':'FROZEN','manifest':str(p),'sha256':sha(b),'rows':len(rows),'full_payload_bytes':sum(r['bytes'] for r in rows),'manifest_bytes':len(b)}))
