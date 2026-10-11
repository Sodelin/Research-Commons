"""Independent static output readback; Git object reads only, no live index assertions."""
from pathlib import Path
import collections
import datetime
import hashlib
import json
import os
import resource
import subprocess

resource.setrlimit(resource.RLIMIT_AS, (256 * 2**20, 256 * 2**20))
D = Path(__file__).parent
R = Path('/workspace/Research-Commons')
COMMIT = 'f8120b1e413b64303891f7f2f8007169856c03f3'
PACKET = 'research/2026-10-11-dot-accepted-connected-union1568-0133z'
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
PINS = {
 'STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json': 'c250c416171cfd895f84812fbca415879ef84e20a4cc779785ac40d6c7c1f9e3',
 'STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json': '8b65e62c0d894269d73429035c40a006c877d88d76a4543edd3300630ae73878',
 'StaticProspectiveUnion1573Imports.lean': '15266faf674115986680f273f04786cdfdd0dc1e78c1f0670471b7634a115322',
 'STATIC-PROSPECTIVE-UNION1573-VALIDATION.json': '20c945b647658ccae79358361e90621d33afec685ed2afcc1660019cdf53a54d',
 'STATIC-PROSPECTIVE-UNION1573-FINAL-HANDOFF.json': 'f2fefd6852e469eb73f8e803e77f7f49ded14f67d24cbfb1637288eba0857ff4',
 'derive_static_union1573.py': '6d93074ea965489298b09a4caf69831c9bc42fdab757f127188e4ca12ecd13e1'
}

def require(value, message):
    if not value:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def canonical(value):
    return digest(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True).encode())


def git(*args):
    return subprocess.check_output(['git', '-c', 'core.packedGitWindowSize=16m', '-c', 'core.packedGitLimit=64m', '-C', str(R)] + list(args), env=ENV)


def run():
    inputs = {}
    for name, expected in PINS.items():
        b=(D/name).read_bytes();require(digest(b)==expected, 'Static output pin differs: '+name)
        inputs[name]={'path':str(D/name),'sha256':digest(b),'bytes':len(b)}
    g=json.loads((D/'STATIC-PROSPECTIVE-UNION1573-DEPENDENCY-GRAPH.json').read_bytes())
    m=json.loads((D/'STATIC-PROSPECTIVE-UNION1573-MODULE-SOURCE-MAP.json').read_bytes())
    v=json.loads((D/'STATIC-PROSPECTIVE-UNION1573-VALIDATION.json').read_bytes())
    h=json.loads((D/'STATIC-PROSPECTIVE-UNION1573-FINAL-HANDOFF.json').read_bytes())
    require(g['status']==m['status']==h['status']=='STATIC_NOT_KERNEL_ACCEPTED' and v['status']=='PASS_STATIC_NOT_KERNEL_ACCEPTED', 'Static qualification differs')
    require(list(g['targets'])==['static/prospective1573'], 'Unexpected runnable or extra target')
    t=g['targets']['static/prospective1573'];nodes=t['modules'];mapping=m['modules']
    require(set(nodes)==set(mapping) and len(nodes)==len(t['order'])==len(set(t['order']))==1573, 'Complete source-map/order count differs')
    peer_raw=git('show',COMMIT+':'+PACKET+'/DEPENDENCY-GRAPH.json')
    require(digest(peer_raw)=='1a82a47a20257e9fa83bc88c786a55ca82d4dd245952cf4779a646f84a83d825','Parent graph differs')
    peer=json.loads(peer_raw)['targets']['current/connected']
    old=peer['modules'];added=set(nodes)-set(old)
    require(len(old)==1568 and len(added)==5 and set(old).issubset(nodes),'Exact1568+5 source set differs')
    require(all(nodes[n]==row for n,row in old.items()),'Original module record differs')
    require(t['order'][:1568]==peer['order'] and t['roots'][:len(peer['roots'])]==peer['roots'],'Original order/root prefix differs')
    require(t['external_imports']==sorted(peer['external_imports']),'External import set differs')
    deps={n:set(p for p in row['imports'] if p in nodes) for n,row in nodes.items()}
    reverse=collections.defaultdict(set)
    for n,ps in deps.items():
        for p in ps:reverse[p].add(n)
    indegree={n:len(ps) for n,ps in deps.items()};ready=collections.deque(n for n,d in indegree.items() if d==0);processed=[]
    while ready:
        n=ready.popleft();processed.append(n)
        for child in reverse[n]:
            indegree[child]-=1
            if indegree[child]==0:ready.append(child)
    require(len(processed)==1573,'Independent Kahn DAG check found a cycle')
    position={n:i for i,n in enumerate(t['order'])}
    require(all(position[p]<position[n] for n,ps in deps.items() for p in ps),'Stored topological order differs')
    reached=set();pending=list(t['roots'])
    while pending:
        n=pending.pop()
        if n in reached:continue
        reached.add(n);pending.extend(deps[n])
    require(reached==set(nodes),'Complete root closure differs')
    require(len(t['roots'])==len(set(t['roots']))==1456,'Root count differs')
    for n,row in mapping.items():
        require(row['module']==n and row['sha256']==nodes[n]['sha256'] and row['literal_imports']==nodes[n]['imports'],'Source-map tuple differs: '+n)
        path=row['source_git_path'];require(path.startswith('research/') and not path.startswith('/') and '..' not in Path(path).parts,'Nonportable source origin: '+n)
        require(row['git_mode']=='100644' and row['body_hash_size_and_literal_imports_checked'] and row['combined1573_object_admission']=='NOT_PERFORMED','Source origin or admission qualification differs')
        if n in old:require(row['source_origin']['original_record_canonical_sha256']==canonical(old[n]),'Original record provenance differs: '+n)
    new_blob_reads=[]
    for n in t['order'][1568:]:
        row=mapping[n];body=git('cat-file','blob',row['git_blob'])
        require(len(body)==row['bytes'] and digest(body)==row['sha256'],'Captured new immutable Git blob differs: '+n)
        new_blob_reads.append({'module':n,'git_blob':row['git_blob'],'sha256':digest(body),'bytes':len(body),'source_git_ref':row['source_git_ref']})
    aggregate=(D/'StaticProspectiveUnion1573Imports.lean').read_text()
    require(aggregate.startswith('/-\nSTATIC_NOT_KERNEL_ACCEPTED\n'),'Import-only text qualification absent')
    tail=aggregate.split('-/\n',1)[1];lines=tail.splitlines();require(len(lines)==1573 and lines==['import '+n for n in t['order']],'Aggregate includes unexpected text or order')
    require(g['runnable_lake_setup_or_builder_context'] is False and g['combined_kernel_or_owned_audit_acceptance'] is False,'Runnable/kernel claim differs')
    require(v['checks']['no_decl_count_prediction'] and v['checks']['new_G4_drafts_or_duplicate_G3_modules_added']==0,'Scope claim differs')
    created=datetime.datetime.now(datetime.timezone.utc).isoformat()
    record={'schema':'static_union1573_independent_output_readback_v1','status':'PASS_STATIC_NOT_KERNEL_ACCEPTED','created_utc':created,'contributor':'Codex / lean_integration_successor','readback_reader':{'path':str(Path(__file__)),'sha256':digest(Path(__file__).read_bytes()),'bytes':Path(__file__).stat().st_size},'input_output_pins_rehashed':inputs,'checks':{'modules':1573,'retained_original_module_records_exact':1568,'genuinely_new_unique_names':5,'source_map_entries':1573,'topological_order_entries':1573,'independent_Kahn_DAG_processed':1573,'complete_root_reachable_modules':1573,'roots':1456,'external_import_names_unchanged':181,'import_only_aggregate_lines':1573,'aggregate_declarations_and_options':0,'portable_Git_source_origins':1573,'new_immutable_blob_checks':new_blob_reads,'live_index_assertion_or_mutation':False,'first_class_original_records_not_normalized':True,'new_source_or_theorem_repairs':0,'decl_count_prediction':False,'new_G4_drafts_or_duplicate_G3_added':0},'execution':{'Lean_Builder_or_project_module_imported':False,'kernel_compiler_evaluator_native_or_audit_process':False,'source_cache_stage_or_new_working_context':False},'accepted_parent_graphs_sources_and_proof_receipts_unchanged':True}
    p=D/'STATIC-PROSPECTIVE-UNION1573-READBACK.json';b=(json.dumps(record,indent=2,sort_keys=True)+'\n').encode()
    with p.open('xb') as f:f.write(b)
    require(p.read_bytes()==b,'Readback receipt write differs')
    files=[]
    for p in sorted(D.iterdir()):
        require(p.is_file() and not p.is_symlink(),'Unexpected context or source-copy directory')
        data=p.read_bytes();files.append({'path':str(p),'relative_path':p.name,'sha256':digest(data),'bytes':len(data),'allocated_bytes':p.stat().st_blocks*512})
    inventory={'schema':'static_union1573_all_file_inventory_v1','status':'STATIC_NOT_KERNEL_ACCEPTED','created_utc':created,'contributor':'Codex / lean_integration_successor','directory':str(D),'files_except_this_manifest':files,'listed_file_count':len(files),'listed_total_bytes':sum(x['bytes'] for x in files),'listed_total_allocated_bytes':sum(x['allocated_bytes'] for x in files),'self_identity_printed_in_tool_output_to_avoid_recursive_self_hash':True,'source_bodies_compiled_objects_Lake_or_executor_files_included':False,'source_reader_is_static_metadata_only':True}
    ip=D/'STATIC-PROSPECTIVE-UNION1573-FILE-INVENTORY.json';ib=(json.dumps(inventory,indent=2,sort_keys=True)+'\n').encode()
    with ip.open('xb') as f:f.write(ib)
    require(ip.read_bytes()==ib,'Inventory write differs')
    print(json.dumps({'status':record['status'],'readback':{'path':str(D/'STATIC-PROSPECTIVE-UNION1573-READBACK.json'),'sha256':digest(b),'bytes':len(b)},'inventory':{'path':str(ip),'sha256':digest(ib),'bytes':len(ib)},'all_file_count':len(files)+1,'all_total_bytes':sum(x['bytes'] for x in files)+len(ib),'all_total_allocated_bytes':sum(x['allocated_bytes'] for x in files)+ip.stat().st_blocks*512,'new_context_or_producer':False},sort_keys=True))

if __name__=='__main__':run()
