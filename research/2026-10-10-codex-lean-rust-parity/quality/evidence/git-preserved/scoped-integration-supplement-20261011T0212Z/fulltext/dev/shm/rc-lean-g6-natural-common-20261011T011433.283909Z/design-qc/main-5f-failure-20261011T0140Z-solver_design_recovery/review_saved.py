#!/usr/bin/env python3
"""Read-only preserved failure/capture and cache authentication; no target imports."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re
import sys

P=Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
W=Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z')
R=W/'.build/runs/20261011T012303.766984Z'
F=W/'lossless-export/main-5f-failed-20261011T012303.766984Z'
TARGET='extraction/g6-natural-common-forest-factorization-5f0143f9'
TD=R/'targets/extraction_g6-natural-common-forest-factorization-5f0143f9'
SOURCE='5f0143f9f266659cb35c495c3bbb01781039d1338a2eb527e1196bd419b6c4f9'

def require(ok, label):
    if not ok:
        raise AssertionError(label)

def digest(b):
    return hashlib.sha256(b).hexdigest()

def pin(path, expected=None):
    p=Path(path)
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):
            h.update(b)
    require(expected is None or h.hexdigest()==expected,'pin '+str(p))
    return {'path':str(p),'bytes':p.stat().st_size,'sha256':h.hexdigest()}

def load(path):
    return json.loads(Path(path).read_bytes())

def companion(p,s):
    return p.with_suffix(s) if s in ('.olean','.ilean','.ir') else Path(str(p)+s[len('.olean'):])

def bundle(path,expected):
    p=Path(path)
    require({s for s in ('.olean','.olean.private','.olean.server','.ilean','.ir') if companion(p,s).is_file()}==set(expected),'complete companion inventory')
    return {s:pin(companion(p,s),h) for s,h in expected.items()}

def check():
    prep_qc=pin(W/'design-qc/natural-v9-preparation-20261011T0118Z-solver_design_recovery/V9-ACTUAL-PREPARATION-SAVED-QC-ATTEMPT1.json','bd8b66e2f5491ae836c07683dcecb6d90efc8fbf03425d363402d5c8aea78693')
    result_pin=pin(W/'G6-NATURAL-COMMON-FACTORIZATION-MAIN-5F-FAILED-20261011T012303.766984Z-RESULT.json','a6dafff494b4b6fd93347c9badd8e34bebf7e1a47b7388340780311f8e64d9c3')
    pin(F/'PRESERVATION-MANIFEST.json',result_pin['sha256'])
    m=load(result_pin['path'])
    E=Path(m['evidence'])
    pin(E/'PRESERVATION-MANIFEST.json',result_pin['sha256'])
    require(m['status']=='INCOMPLETE_TARGET_FAILURES_PRESERVED' and not m['packet_distribution_complete'] and m['lossless_distribution']=='FIXED_SHMEM_EXPORT_ONLY_EXPLICIT_CAPACITY_BOUNDARY' and m['actual_run']==str(R) and m['complete_lossless_export_original']==str(F),'exact actual failed run and complete fixed-shmem export; packet explicitly absent')
    require(not m['compiled_artifact_bytes_distributed'] and not m['original_attempts_overwritten'] and not m['protected_provider_context_executed'],'no distributed compiled bytes/attempt overwrite/guard execution')
    rows=m['preserved_files']
    require(len(rows)==len({x['path'] for x in rows})==51,'51 unique preserved rows')
    compared=[]
    compressed=[]
    for row in rows:
        rel=Path(row['path'])
        require(not rel.is_absolute() and '..' not in rel.parts,'relative evidence paths')
        fp,ep,op=pin(F/rel,row['sha256']),pin(E/rel,row['sha256']),pin(row['original_path'],row['original_sha256'])
        require(fp['bytes']==ep['bytes']==row['bytes'] and F==E,'manifest fixed path and full-byte identity')
        encoded=(F/rel).read_bytes()
        require(encoded[:4]!=b'\x7fELF','zero exported ELF')
        if row.get('encoding')=='gzip':
            decoded=gzip.decompress(encoded)
            require(decoded==Path(row['original_path']).read_bytes() and digest(decoded)==row['restored_sha256']==op['sha256'] and len(decoded)==row['restored_bytes']==op['bytes'],'complete restored EOF/bytes/hash identical retained original')
            compressed.append(row)
        else:
            require(encoded==Path(row['original_path']).read_bytes(),'complete raw original byte equality')
        compared.append({'stored_fixed':fp,'stored_packet':ep,'original':op})
    dp=pin(F/'COMPRESSED-DISTRIBUTIONS.json',m['compressed_distributions_manifest_sha256'])
    pin(E/'COMPRESSED-DISTRIBUTIONS.json',dp['sha256'])
    distribution=load(dp['path'])
    require(distribution['distributions']==compressed and distribution['original_run_unchanged'] and sum(x['bytes'] for x in rows)+dp['bytes']==m['measured_export_bytes_before_manifest']==829073,'exact lossless distribution/payload')
    expected={x['path'] for x in rows}|{'PRESERVATION-MANIFEST.json','COMPRESSED-DISTRIBUTIONS.json'}
    require({str(p.relative_to(F)) for p in F.rglob('*') if p.is_file()}==expected and {str(p.relative_to(E)) for p in E.rglob('*') if p.is_file()}==expected,'all53 fixed-shmem file inventory')
    capacity=m['overlay_capacity_preflight']
    require(capacity['transient_reserve_bytes']==8388608 and not capacity['source_or_evidence_deleted'] and capacity['free_before_bytes']>=capacity['transient_reserve_bytes'] and capacity['free_before_bytes']<capacity['transient_reserve_bytes']+capacity['measured_payload_bytes']+capacity['manifest_and_result_reserve_bytes'],'dated fixed-shmem fallback preserves unchanged8MiB reserve'); require(m['natural_exporter_v3_storage_location_derivation']['packet_copy_disabled'] and m['natural_exporter_v3_storage_location_derivation']['result_directory']==str(W) and m['exporter_sha256']=='cb9826d672dde47dd4beb8fa5f739a1d365d06c416ccf38737859a46c3217b04','explicit reviewed location-only exporter no packet copy')
    require(sum(p.stat().st_size for p in F.rglob('*') if p.is_file())==860013,'exact full53file byte total'); pin(P/'lean/scripts/build_connected.py','13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'); pin(Path('/dev/shm/rc-lean-g6-natural-common-20261011T005738.287542Z')/'design-qc/natural-v9-and-output-helpers-20261011T0114Z-solver_design_recovery/V9-AND-SHMEM-OUTPUT-STATIC-QC-ATTEMPT2.json','557186c0e928aa3a08248371787ca42593117f0f1a02688b4b6a245c0be3a2ce'); pin(Path('/dev/shm/rc-lean-g6-natural-common-20261011T005738.287542Z')/'scripts/preserve_g6_natural_common_20261011_v3_shmem_metadata.py',m['exporter_sha256'])
    final=load(R/'FINAL-RECEIPT.json')
    require(final==m['final_receipt'] and final['status']=='INCOMPLETE_TARGET_FAILURES_PRESERVED' and final['targets_requested']==[TARGET] and final['targets_passed']==[] and final['counts']=={'cache_reuse':140} and final['trust_level']==0 and final['kernel_checking'] and final['compiler_identity_stable'] and final['native_runtime_final_rehash_stable'],'exact140warm nofresh admitted/no complete target')
    a=R/'attempts/00001-G6NaturalCommonForestFactorization'
    require({p.name for p in (R/'attempts').iterdir()}=={a.name},'only one failed main attempt; no aggregate/audit')
    recpin=pin(a/'receipt.json','5a720018343ddea62a7f04c5e35bccff149208855e2ebcaf132f58f42e0f597e')
    rec=load(recpin['path'])
    descriptor=pin(a/'STDERR-CAPTURE.json')
    cap=load(descriptor['path'])
    require(rec['stderr_storage']==cap and cap['complete'] and cap['eof'] and not cap['truncated'] and cap['reason'] is None and cap['exit_code']==rec['exit_code']==1,'complete nontruncated actualfailed livecapture')
    gp=pin(a/'stderr.raw.gz','979f720bb7e93dda1047efa3a41cc88f61819e1a2a6e08d02501f7bdeb8f873b')
    raw=gzip.decompress(Path(gp['path']).read_bytes())
    require(gp['bytes']==cap['gzip_bytes']==291825 and digest(raw)==cap['raw_sha256']==rec['stderr_sha256']=='ad403abbc1651f67ceb61901476b63aeb5d01d0b93f9219ca0fba6e4f483f2ad' and len(raw)==cap['raw_bytes']==12617424,'full raw/encoded identities EOF/bounds')
    require(not (a/'stderr').exists(),'no separate raw live capture claimed')
    native=load(R/'NATIVE-RUNTIME-PINS.json')
    current=[]
    for path,row in native['libraries'].items():
        pp=pin(path,row['sha256']);s=Path(path).stat()
        require(pp['bytes']==row['bytes'] and [s.st_dev,s.st_ino,s.st_size,s.st_mtime_ns,s.st_ctime_ns]==row['stat_identity'],'all current native bytes/stat')
        current.append(pp)
    hashes={k:v['sha256'] for k,v in native['libraries'].items()}
    nf=load(R/'NATIVE-RUNTIME-FINAL-REHASH.json')
    require(len(current)==28 and nf['stable'] and nf['hashes']==hashes and digest(json.dumps(hashes,sort_keys=True).encode())==native['native_runtime_digest']==rec['native_runtime_digest']==final['native_runtime_digest'],'all28 initial/final/current native identities')
    names=re.findall(rb'calling init:\s*(\S+)',raw)
    resolved={str(Path(n.decode()).resolve()) for n in names}
    require(len(names)==len(resolved)==10 and resolved==set(rec['native_initialized_libraries']) and rec['native_initialized_libraries_bound'] and all(rec['native_initialized_libraries'][k]==native['libraries'][k] for k in resolved),'ten full actual initialized native identities')
    require(rec['native_loader_outputs']==[{'path':gp['path'],'sha256':gp['sha256'],'encoding':'gzip','raw_sha256':digest(raw),'raw_bytes':len(raw)}],'exact actualnative evidenceframe')
    stdoutpin=pin(a/'stdout','44a0b362bf2e1033f9a1108c040bda3860814b1bbc1b062be12f8bbb6a6ac13f')
    stdout=Path(stdoutpin['path']).read_text()
    locations=[list(map(int,x)) for x in re.findall(r'^G6NaturalCommonForestFactorization\.lean:(\d+):(\d+): error',stdout,re.M)]
    require(locations==[[297,76]] and stdout.count('sorryAx')==2,'exact one ordinary ifTrue proof goal and two diagnostic sorry prints retained')
    require(rec['status']=='FAILED_OR_RESOURCE' and 'object_artifacts' not in rec and not (a/'G6NaturalCommonForestFactorization.olean').exists(),'no successful factorization object/cache admission')
    require(rec['source_sha256']==SOURCE and rec['cap_memory_mib']==4096 and rec['cap_seconds']==180 and all(x in rec['command'] for x in ('-j1','-t0','-M4096','-Ddebug.skipKernelTC=false')) and rec['source_and_imports_stable'] and rec['native_runtime_stat_stable'],'actualstrict unchanged4GiB180s inputs/flags')
    sourcepin=pin(a/'work/G6NaturalCommonForestFactorization.lean',SOURCE)
    pin(W/('source-store/'+SOURCE+'.lean'),SOURCE)
    require(set(re.findall(r'^import\s+(\S+)',Path(sourcepin['path']).read_text(),re.M))==set(rec['direct_import_bindings']),'actualfailed source literalimport set')
    failedimports=[]
    for name,row in rec['direct_import_bindings'].items():
        bp=bundle(row['path'],row['artifacts'])
        require(row['sha256']==row['artifacts']['.olean']==rec['direct_import_sha256'][name] and row['artifacts']==rec['direct_import_artifacts'][name],'failedactual source bound importbundles')
        failedimports.append({'module':name,'pins':bp})
    graph=load(W/'DEPENDENCY-GRAPH.json')
    target=load(TD/'RESULT.json')
    components=target['component_receipts']
    require(target['status']=='FAILED_OR_BLOCKED' and target['error']=='Component failed G6NaturalCommonForestFactorization' and len(components)==len({x['module'] for x in components})==140 and {x['module'] for x in components}==set(graph['targets'][TARGET]['modules'])-{'G6NaturalCommonForestFactorization'},'all140 exact prior admissions;141 target incomplete')
    checked=[]
    for c in components:
        require(not c['receipt_directory'].startswith(str(R)+'/') and c['exit_code']==0 and c['source_sha256']==graph['targets'][TARGET]['modules'][c['module']]['sha256'],'all140 warm prior successes source exactgraph')
        sp=pin(W/('source-store/'+c['source_sha256']+'.lean'),c['source_sha256'])
        require(re.findall(r'^(?:public\s+)?import\s+([A-Za-z_][A-Za-z0-9_.]*)',Path(sp['path']).read_text(),re.M)==graph['targets'][TARGET]['modules'][c['module']]['imports'],'every admitted literal import list')
        cache=Path(c['cached_object']).parent/'receipt.json'
        require(load(cache)==c,'all140 target and cache records exact')
        checked.append({'module':c['module'],'source':sp,'receipt':pin(cache),'objects':bundle(c['cached_object'],c['object_artifacts'])})
    prefix=next(x for x in components if x['module']=='G6OriginalCommonPrefix')
    require(Path(prefix['cached_object']).parent.name=='54ae5d6ce3d15200690415bbd1279d656cc4bfd4afa654a9d4a8f01f81bb95a9' and prefix['source_sha256']=='a080722170d367fe9aa7420c5c5488fe4c7df73a6d994aba15346a8d2ee4c917','qualifieda080 strict key unchanged')
    prep=load(W/'PREPARATION.json')
    gatepins=[pin(x['path'],x['sha256']) for x in prep['additional_storage_input_pins'].values()]
    guarddir=next((W/'guard-runs').iterdir())
    prelaunch=[pin(x['path'],x['sha256']) for x in load(guarddir/'PRE-PHASE-INPUT-PINS.json').values()]
    guard=load(guarddir/'RECEIPT.json');plan=load(W/'RESOURCE-AND-RUN-PLAN.json')
    require(guard['exit_code']==1 and guard['abort_reason'] is None and guard['monitor_error'] is None and not guard['resource_caps_kernel_flags_core_or_audit_changed'] and guard['peak_distinct_inode_allocation_bytes']<plan['scratch_abort_bytes'] and guard['peak_nonreclaimable_estimate_bytes']<plan['memory_abort_bytes'],'ordinary proof failure, no resource abort or changed policy')
    require(guard['config_sha256']==pin(W/'RESOURCE-AND-RUN-PLAN.json')['sha256'] and guard['monitor_sha256']=='8a190dfa60b0151c1ad622fab21eefac866b44145a1d0d3665b31f66a1979a9b','actual plan/monitor exact')
    compiler=pin(rec['command'][0],final['compiler_sha256'])
    storage=load(R/'COMPRESSED-STDERR-STORAGE-PINS.json')
    equivalence=load(W/'PARENT-WRAPPER-EQUIVALENCE.json')
    require(storage['same_core_module_object'] and storage['adapter_sha256']=='d774eb292aa0b819791458c51a9353885d3d31b2bde781b85b3c26829e61c810' and storage['authenticated_parent_sha256']==equivalence['actual_authenticated']['sha256'] and storage['namespace_parent_sha256']==equivalence['actual_namespace']['sha256'],'actualsamecore/namespace/authenticated composition unchanged')
    return {'status':'PASS_SAVED_SIXTH_MAIN_5F_PROOF_FAILURE_COMPLETE_CAPTURE_AND_QUALIFIED_PREFIX_REUSE_QC','prior_prepared_qc':prep_qc,'preservation_result':result_pin,'distribution_manifest':dp,'all_export_original_comparisons':compared,'file_counts':{'rows':51,'fixed_files':53,'packet_files':0,'gzip_restorations':len(compressed),'payload_bytes':829073,'packet_distribution_complete':False,'ELFs':0},'actual_attempt':recpin,'capture_descriptor':descriptor,'encoded_capture':gp,'raw_identity':{'bytes':len(raw),'sha256':digest(raw),'full_gzip_eof':True,'initialized_paths':sorted(resolved)},'stdout':stdoutpin,'actual_errors':locations,'diagnostic_sorry_prints':2,'current28native':current,'compiler':compiler,'actual_source':sourcepin,'failed_actual_imports':failedimports,'admitted140component_pins':checked,'qualified_prefix_cache_key':Path(prefix['cached_object']).parent.name,'prelaunchpins':prelaunch,'additional_gatepins':gatepins,'guard':pin(guarddir/'RECEIPT.json'),'qualification':['Capture/preservation PASS; Lean factorization failed at one ifTrue proof goal with two diagnostic sorry prints, all retained. No successful factorization object, aggregate or owned audit, no141 acceptance.', '140 actual warm admissions comprise139 accepted parent providers plus separately qualifieda080 kernel component; no newsource-version or currentfreshness/parent-root acceptance inferred.', 'Complete51-row fixed-shmem-only preservation is explicit. Encoded/distribution bytes are829073;53 actual files including preservation manifest total860013. The result does not claim a packet copy. Later Git publication must keep this historical storage result unchanged.', 'Source/input/core/storage/strict kernel/resource policy unchanged. No compiler/helper/Builder/target module imported or invoked by this reader.']}

def main():
    report={'schema':'natural_main_5f_failure_saved_design_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':pin(__file__)['sha256'],'target_modules_imported_or_producer_processes_started':0,'mathematical_acceptance_modified':False}
    try:
        report.update(check())
    except Exception as e:
        report.update(status='FAIL_SAVED_QC',error=str(e),error_type=type(e).__name__)
    out=Path(sys.argv[1])
    with out.open('x') as f:
        json.dump(report,f,indent=2,sort_keys=True)
        f.write('\n')
    print(json.dumps({'status':report['status'],'path':str(out),'sha256':pin(out)['sha256']}))
    return int(report['status']=='FAIL_SAVED_QC')

if __name__=='__main__':
    raise SystemExit(main())
