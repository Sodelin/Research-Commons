"""Thin static1575 source plan. Only read fixed Git blobs; never stage or run Lean."""
from pathlib import Path
import ast, datetime, hashlib, json, os, re, resource, subprocess
resource.setrlimit(resource.RLIMIT_AS,(256*2**20,256*2**20))
ROOT=Path('/workspace/Research-Commons')
OUT=Path(__file__).parent
OLD=OUT.parent/'static-union1573-source-plan-20261011T022330.460416Z'
COMMIT='62020166e3e7ef690838f50b13caa149ede419ec'
PACKET='research/2026-10-11-dot-accepted-connected-union1570-g4span-0225z'
LEAN='research/2026-10-10-codex-lean-rust-parity/lean'
QC=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/connected1570-readonly-review-20261011T0238Z/PUBLIC-CONNECTED1570-READONLY-REVIEW-ATTEMPT1.json')
QSHA='c92c6be19d13504c25447f353142864225942b1e1baeb1df9d55cdf25f8a5162'
HAND=LEAN+'/FIVE-ACCEPTED-ADDITIONS-FOR-UNION1573-HANDOFF-20261011T0204Z.json'
HSHA='a8da11f75c80dffde842ac6f982a119dc32ca8188269aca90cb1339d39056f9d'
PINS={
 'STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json':'c250c416171cfd895f84812fbca415879ef84e20a4cc779785ac40d6c7c1f9e3',
 'STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json':'8b65e62c0d894269d73429035c40a006c877d88d76a4543edd3300630ae73878',
 'derive_static_union1573.py':'6d93074ea965489298b09a4caf69831c9bc42fdab757f127188e4ca12ecd13e1'}
GIT=['git','-c','core.packedGitWindowSize=16m','-c','core.packedGitLimit=64m','-C',str(ROOT)]
ENV=dict(os.environ,GIT_OPTIONAL_LOCKS='0')
def require(ok,msg):
    if not ok: raise ValueError(msg)
def sha(b): return hashlib.sha256(b).hexdigest()
def csha(x): return sha(json.dumps(x,sort_keys=True,separators=(',',':')).encode())
def identity(p):
    b=p.read_bytes();return {'path':str(p),'sha256':sha(b),'bytes':len(b)}
def checked(p,h):
    b=p.read_bytes();require(sha(b)==h,'pin differs: '+str(p));return b
def git(*a):return subprocess.check_output(GIT+list(a),env=ENV)
def pub(n):return git('show',COMMIT+':'+PACKET+'/'+n)
def save(n,v):
    b=(json.dumps(v,sort_keys=True,indent=2)+'\n').encode();p=OUT/n
    with p.open('xb') as f:f.write(b)
    return identity(p)
def literal_imports(text):
    """Remove nested Lean block/line comments before reading import lines."""
    out = []
    depth = 0
    i = 0
    quoted = False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == '/-':
                depth += 1
                i += 2
            elif pair == '-/':
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i + 1])
                i += 2
            else:
                if text[i] == '"':
                    quoted = False
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i))
            i = end
        else:
            out.append(text[i])
            if text[i] == '"':
                quoted = True
            i += 1
    require(depth == 0, 'Unclosed source block comment')
    imports = []
    for line in ''.join(out).splitlines():
        stripped = line.strip()
        if stripped.startswith('public '):
            stripped = stripped[7:].lstrip()
        if stripped.startswith('import '):
            imports.extend(stripped[7:].split())
    return imports

def main():
    old_before={p.name:identity(p) for p in OLD.iterdir() if p.is_file()}
    values={n:checked(OLD/n,h) for n,h in PINS.items()}
    oldg=json.loads(values['STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json'])['targets']['static/prospective1573']
    oldmap=json.loads(values['STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json'])['modules']
    parser_old=next(n for n in ast.parse(values['derive_static_union1573.py']).body if isinstance(n,ast.FunctionDef) and n.name=='literal_imports')
    own=Path(__file__).read_text();parser_new=next(n for n in ast.parse(own).body if isinstance(n,ast.FunctionDef) and n.name=='literal_imports')
    require(ast.dump(parser_old,include_attributes=False)==ast.dump(parser_new,include_attributes=False),'parser changed')
    hb=checked(ROOT/HAND,HSHA);handoff=json.loads(hb);five=handoff['safe_new_only_topological_order']
    qb=checked(QC,QSHA);q=json.loads(qb);require(q['status'].startswith('PASS_EXACT_PUBLIC_GRAPH'),'public1570 review not PASS')
    gb=pub('DEPENDENCY-GRAPH.json');require(sha(gb)=='ba9148757fda063c86b40db0d453a3eccd85c224800a8b98ebd12f6ffe31f367','peer graph changed')
    peer=json.loads(gb)['targets']['current/connected'];pm=peer['modules']
    mb=pub('MANIFEST.json');require(sha(mb)=='ddeb64940618cf3253971c47380c807145fdc2e9b2516e06d5bd3942a3f41587','manifest changed')
    manifest={r['path']:r for r in json.loads(mb)['files']}
    ab=pub('ACCEPTANCE.json');require(sha(ab)=='ce2a64c47885084ff52279da8242f16dccdb25eeeac89b7675478692156cdc64','acceptance changed')
    accepted=json.loads(ab);require(accepted['modules']==1570 and accepted['graph_sha256']==sha(gb),'acceptance graph differs')
    base=set(oldg['modules'])-set(five);pair=set(pm)-base
    require(len(base)==1568 and len(pm)==1570 and len(five)==5 and len(set(five))==5,'module counts differ')
    require(pair=={'G4ActualOriginalSpanDiagonal','G4ActualOriginalSpanNaturalAverage'},'new peer pair differs')
    require(not set(five)&set(pm),'five already in peer base')
    require(all(pm[n]==oldg['modules'][n] for n in base),'inherited module dictionary differs')
    require([n for n in peer['order'] if n in base]==[n for n in oldg['order'] if n in base],'inherited order differs')
    require([n for n in peer['roots'] if n in base]==[n for n in oldg['roots'] if n in base],'inherited roots differ')
    require(peer['external_imports']==oldg['external_imports'],'external list differs')
    tree={}
    for line in git('ls-tree','-r','-z',COMMIT,'--',PACKET+'/source-store/').split(b'\0'):
        if line:
            a,p=line.split(b'\t',1);mode,kind,blob=a.decode().split();require(mode=='100644' and kind=='blob','nonregular peer source')
            tree[p.decode()]=blob
    specs=[];new_records=[];acceptance_inputs=[]
    for n in peer['order']:
        r=pm[n];path=PACKET+'/source-store/'+r['sha256']+'.lean';m=manifest[path[len(PACKET)+1:]]
        require(m['sha256']==r['sha256'] and tree[path]==m['git_blob'],'manifest/blob binding differs')
        specs.append((n,r['sha256'],m['bytes'],r['imports'],m['git_blob']))
        if n in pair:
            new_records.append({'module':n,'sha256':r['sha256'],'bytes':m['bytes'],'imports':r['imports'],'source_git_path':path,'git_blob':m['git_blob'],'source_git_commit':COMMIT,'original_peer_module_record':r})
        else:
            old=oldmap[n];require((old['sha256'],old['bytes'],old['literal_imports'])==(r['sha256'],m['bytes'],r['imports']),'captured inherited source tuple differs')
    sources={r['module']:r for r in handoff['sources']}
    five_records=[]
    for n in five:
        r=oldmap[n];h=sources[n]
        require(all(r[k]==h[k] for k in ['module','sha256','bytes','literal_imports','source_git_path']),'five handoff tuple differs')
        ar=r['accepted_scope_origin'];checked(ROOT/ar['source_git_path'],ar['sha256']);acceptance_inputs.append(ar)
        specs.append((n,r['sha256'],r['bytes'],r['literal_imports'],r['git_blob']))
        five_records.append({k:r[k] for k in ['module','sha256','bytes','literal_imports','source_git_path','git_blob','source_git_ref','accepted_scope_origin']})
    total=0
    proc=subprocess.Popen(GIT+['cat-file','--batch'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,env=ENV)
    try:
        for n,h,size,imports,blob in specs:
            proc.stdin.write((blob+'\n').encode());proc.stdin.flush()
            line=proc.stdout.readline().decode().strip().split();require(line==[blob,'blob',str(size)],'blob response differs: '+n)
            body=proc.stdout.read(size);require(proc.stdout.read(1)==b'\n','blob terminator differs')
            require(len(body)==size and sha(body)==h and literal_imports(body.decode())==imports,'body/import differs: '+n)
            total+=size
        proc.stdin.close();require(proc.wait()==0,'cat-file failed')
    finally:
        if proc.poll() is None:proc.terminate();proc.wait()
    modules=dict(pm);modules.update({n:oldg['modules'][n] for n in five})
    order=peer['order']+five;roots=peer['roots']+five
    require(len(order)==1575 and len(set(order))==1575 and set(order)==set(modules),'order not exact')
    require(len(set(roots))==len(roots) and set(roots)<=set(modules),'roots not unique/subset')
    pos={n:i for i,n in enumerate(order)};edges={(n,d) for n in order for d in modules[n]['imports'] if d in modules}
    require(all(pos[d]<pos[n] for n,d in edges),'DAG/order violated')
    external=sorted({d for n in order for d in modules[n]['imports'] if d not in modules})
    require(set(external)==set(peer['external_imports']),'unresolved/new external import')
    visited=set();todo=list(roots)
    while todo:
        n=todo.pop()
        if n not in visited:visited.add(n);todo.extend(d for d in modules[n]['imports'] if d in modules)
    require(visited==set(modules),'roots do not cover all modules')
    require({p.name:identity(p) for p in OLD.iterdir() if p.is_file()}==old_before,'old1573 file changed')
    checked(QC,QSHA);checked(ROOT/HAND,HSHA)
    for ar in acceptance_inputs:checked(ROOT/ar['source_git_path'],ar['sha256'])
    tuples=[[n,modules[n]['sha256'],modules[n]['imports']] for n in order]
    counts={'peer_base_modules':1570,'inherited_original1568':1568,'new_peer_G4':2,'separate_cloud_additions':5,'prospective_modules':1575,'roots':len(roots),'internal_DAG_edges':len(edges),'external_imports':len(external)}
    aggregate=('/- STATIC_NOT_KERNEL_ACCEPTED. Import-only prospective1575 source plan.\n'
      'Peer1570 fixed Git base plus five separately accepted cloud sources.\n'
      'No staging, object admission, runnable Lake setup, compiler or combined audit. -/\n'+''.join('import '+n+'\n' for n in order)).encode()
    aggregate_name='StaticProspectiveUnion1575Imports.lean'
    with (OUT/aggregate_name).open('xb') as f:f.write(aggregate)
    inputs={'peer_commit':COMMIT,'peer_graph_git_path':PACKET+'/DEPENDENCY-GRAPH.json','peer_graph_sha256':sha(gb),'peer_manifest_sha256':sha(mb),'peer_reported_acceptance_sha256':sha(ab),'public1570_saved_review':identity(QC),'old1573_graph':old_before['STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json'],'old1573_map':old_before['STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json'],'five_handoff_git_path':HAND,'five_handoff_sha256':HSHA}
    delta=save('STATIC-PROSPECTIVE-UNION1575-SOURCE-PLAN-DELTA.json',{'schema':'thin_static_union1575_source_plan_v1','status':'STATIC_NOT_KERNEL_ACCEPTED','contributor':'Codex / lean_integration_successor','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'source_inputs':inputs,'counts':counts,'recipe':{'modules':'Use fixed peer current/connected module dictionaries without changes, then add the five original old1573 module dictionaries named below.','source_origins':'Every peer body is PACKET/source-store/<sha256>.lean at fixed commit; five bodies use the captured Git blob IDs and Git paths below. No host paths are source origins.','order':'peer current/connected order followed by cloud_addition_order','roots':'peer current/connected roots followed by cloud_addition_order','external_imports':'peer current/connected external_imports unchanged','cloud_addition_order':five,'canonical_order_sha256':csha(order),'canonical_roots_sha256':csha(roots),'canonical_name_sha_import_tuples_sha256':csha(tuples)},'two_peer_G4_records':new_records,'five_separately_accepted_sources':five_records,'aggregate':identity(OUT/aggregate_name),'scope':{'combined1575_kernel_acceptance':False,'compiled_object_or_native_admission':False,'context_staging_cache_or_Git_mutation':False,'runnable_Lake_setup_claim':False,'master_closure':False,'declaration_count_prediction':None,'peer1570_public_gate':'Independent public source/import/full-audit saved review PASS; unavailable private loader/cache payloads are not authenticated or locally admitted.','source_premises':'Individual source premises and formal narrow scopes remain unchanged; natural erasure resets only the selected private COMMON slot and retains other slots/full carried forest.'}})
    validation=save('STATIC-PROSPECTIVE-UNION1575-VALIDATION.json',{'status':'PASS_STATIC_SOURCE_BODY_IMPORT_DAG_AND_PROVENANCE_CHECKS_ONLY','counts':counts,'all1575_fixed_blob_bodies_checked':True,'total_module_body_bytes_read':total,'all1568_original_module_dictionaries_exact':True,'all1568_restricted_order_and_roots_exact':True,'captured_five_blob_ids_only_no_live_index_assertion':True,'five_unique_absent_from1570':True,'complete_DAG_topological_order_and_root_closure':True,'source_or_import_conflicts':[],'all_old1573_file_identities_pre_post':old_before,'public1570_review_pre_post_sha256':QSHA,'producer_source':identity(Path(__file__)),'inherited_parser_source_sha256':PINS['derive_static_union1573.py'],'source_plan_delta':delta,'aggregate':identity(OUT/aggregate_name),'compiler_or_native_processes':0,'Git_mutations':0})
    save('STATIC-PROSPECTIVE-UNION1575-FINAL-HANDOFF.json',{'status':'STATIC_NOT_KERNEL_ACCEPTED','counts':counts,'delta':delta,'validation':validation,'import_only_aggregate':identity(OUT/aggregate_name),'next_action':'An authorized integrator can reconstruct this exact source plan, authenticate its own compatible component/native context, then run a fresh aggregate and full ownership audit. No execution is authorized by this handoff.','preserved_predecessor':'All ten old static1573 files remain byte-identical; this thin1575 plan references the full old map rather than duplicating it.','public1570_saved_review':identity(QC),'not_established':['combined1575 kernel/audit acceptance','private peer native/cache admission','general master closure','runnable Lake context'],'producer_source':identity(Path(__file__))})
    size=sum(p.stat().st_size for p in OUT.iterdir() if p.is_file());require(size<96*2**10,'thin output exceeds96KiB')
    print(json.dumps({'status':'PASS_STATIC_ONLY','counts':counts,'directory':str(OUT),'content_bytes_so_far':size,'aggregate_sha256':sha(aggregate),'delta_sha256':delta['sha256']}))
if __name__=='__main__':main()
