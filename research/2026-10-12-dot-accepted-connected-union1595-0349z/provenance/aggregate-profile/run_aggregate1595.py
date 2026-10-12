#!/usr/bin/env python3
"""Run the unchanged strict builder with measured desktop storage supervision."""
import argparse,hashlib,json,os,resource,shutil,signal,subprocess,time
from pathlib import Path
from completed_trace_transport import compress_completed

ROOT=Path(__file__).resolve().parents[1]
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def allocated(root):
    size=0; largest=0
    for p in root.rglob('*'):
        if p.is_file() and not p.is_symlink():
            s=p.stat();size+=s.st_blocks*512;largest=max(largest,s.st_size)
    return size,largest
def available():
    return int(next(x.split()[1] for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:')))*1024
def limit_event(size,largest,free,mem,cap,floor,perfile):
    if size>=cap:return 'PACKAGE_ALLOCATION_LIMIT'
    if largest>=perfile:return 'PER_FILE_LIMIT'
    if free<floor:return 'FREE_STORAGE_FLOOR'
    if mem<2**30:return 'AVAILABLE_MEMORY_FLOOR'
    return None
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--mathlib',type=Path,required=True)
    ap.add_argument('--lean-bin',type=Path,required=True)
    ap.add_argument('--backing-store',type=Path,default=ROOT)
    ap.add_argument('--target',default='current/connected')
    args=ap.parse_args()
    graph=json.loads((ROOT/'DEPENDENCY-GRAPH.json').read_bytes())
    assert args.target in graph['targets']
    prep=json.loads((ROOT/'PREPARATION.json').read_bytes())
    required_scripts={'run_aggregate1595.py','build_aggregate1595.py','build_streamed_audit.py','audit_stream.py','build_desktop.py','build_with_authenticated_overlay.py','build_with_mathlib_overlay.py','build_connected.py','completed_trace_transport.py','AuditTemplate.lean'}
    if not required_scripts.issubset(prep['scripts']):raise ValueError('Missing exact staged script pins')
    for name in required_scripts:
        script=ROOT/'scripts'/name
        if script.is_symlink() or hashlib.sha256(script.read_bytes()).hexdigest()!=prep['scripts'][name]:raise ValueError('Staged script pin mismatch: '+name)
    for m,e in graph['targets'][args.target]['modules'].items():
        assert hashlib.sha256((ROOT/'source-store'/(e['sha256']+'.lean')).read_bytes()).hexdigest()==e['sha256'],m
    assert hashlib.sha256((ROOT/'DEPENDENCY-GRAPH.json').read_bytes()).hexdigest()==prep['graph_sha256']
    assert available()>=7*2**30,'Insufficient initial memory for existing aggregate/Theta exceptions'
    cap=3*2**30;floor=8*2**30;perfile=512*2**20
    pretransport_size,pretransport_largest=allocated(ROOT)
    pretransport_free=min(shutil.disk_usage(ROOT).free,shutil.disk_usage(args.backing_store).free)
    pretransport_mem=available()
    initial_limit=limit_event(pretransport_size,pretransport_largest,pretransport_free,pretransport_mem,cap,floor,perfile)
    if initial_limit:raise ValueError('Initial pretransport resource limit: '+initial_limit)
    compress_completed(ROOT,force=True)
    start_size,largest=allocated(ROOT)
    storage={'status':'PASS_PREFLIGHT_GUARDED_ALLOCATION_NOT_UNKNOWN_OUTPUT_CERTIFICATION','package_initial_allocated_bytes':start_size,'source_bytes':prep['source_bytes'],'new_g3_source_bytes':prep['new_source_bytes'],'package_path_counted_limit_bytes':cap,'per_file_hard_limit_bytes':perfile,'free_floor_bytes':floor,'package_filesystem_free':shutil.disk_usage(ROOT).free,'backing_store_free':shutil.disk_usage(args.backing_store).free,'dependency_checkout_allocated_bytes':allocated(args.mathlib)[0],'existing_g3_external_observed_peak_bytes':1932623872,'output_reserve_explanation':'3 GiB monitored aggregate-only1595 package allocation; preserved dependency cache separately measured. Unknown compiler output is guarded rather than inferred from source size. No CPU/kernel/memory/time policy changes.'}
    assert min(storage['package_filesystem_free'],storage['backing_store_free'])>cap+floor
    initial_limit=limit_event(start_size,largest,min(storage['package_filesystem_free'],storage['backing_store_free']),available(),cap,floor,perfile)
    if initial_limit:raise ValueError('Initial resource limit: '+initial_limit)
    storage['initial_limit_checks_passed']=True
    storage['initial_pretransport_allocated_bytes']=pretransport_size
    storage['initial_pretransport_free_bytes']=pretransport_free
    storage['script_pins_verified']=sorted(required_scripts)
    save(ROOT/'STORAGE-PREFLIGHT.json',storage)
    env=dict(os.environ,CONNECTED_LEAN_BIN=str(args.lean_bin.resolve()),CONNECTED_MATHLIB=str(args.mathlib.resolve()),PYTHONUNBUFFERED='1')
    cmd=['/usr/bin/python3',str(ROOT/'scripts/build_aggregate1595.py'),args.target]
    def limits():resource.setrlimit(resource.RLIMIT_FSIZE,(perfile,perfile))
    stamp=time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())
    stdout=ROOT/('SUPERVISOR-'+stamp+'.stdout');stderr=ROOT/('SUPERVISOR-'+stamp+'.stderr')
    t=time.monotonic();peak=max(start_size,pretransport_size);lowmem=min(available(),pretransport_mem);lowfree=min(pretransport_free,shutil.disk_usage(ROOT).free,shutil.disk_usage(args.backing_store).free);reason=None
    with stdout.open('wb') as sout,stderr.open('wb') as serr:
        child=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=sout,stderr=serr,start_new_session=True,preexec_fn=limits)
        save(ROOT/'ACTIVE-PROCESS.json',{'pid':child.pid,'process_group':child.pid,'command':cmd,'target':args.target,'started_utc':stamp})
        try:
            while child.poll() is None:
                size,largest=allocated(ROOT);peak=max(peak,size);mem=available();lowmem=min(lowmem,mem);free=min(shutil.disk_usage(ROOT).free,shutil.disk_usage(args.backing_store).free);lowfree=min(lowfree,free)
                reason=reason or limit_event(size,largest,free,mem,cap,floor,perfile)
                if reason is None:
                    try:compress_completed(ROOT)
                    except Exception as ex:reason="TRACE_TRANSPORT_FAILURE: "+repr(ex)
                size,largest=allocated(ROOT);peak=max(peak,size);mem=available();lowmem=min(lowmem,mem);free=min(shutil.disk_usage(ROOT).free,shutil.disk_usage(args.backing_store).free);lowfree=min(lowfree,free)
                reason=reason or limit_event(size,largest,free,mem,cap,floor,perfile)
                if reason:
                    os.killpg(child.pid,signal.SIGTERM)
                    try:child.wait(timeout=10)
                    except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
                    break
                time.sleep(2)
        except Exception as ex:
            reason='SUPERVISOR_EXCEPTION: '+repr(ex)
            if child.poll() is None:
                os.killpg(child.pid,signal.SIGTERM)
                try:child.wait(timeout=10)
                except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
        rc=child.wait()
    try:
        size,largest=allocated(ROOT);peak=max(peak,size)
        free=min(shutil.disk_usage(ROOT).free,shutil.disk_usage(args.backing_store).free);lowfree=min(lowfree,free)
        mem=available();lowmem=min(lowmem,mem)
        reason=reason or limit_event(size,largest,free,mem,cap,floor,perfile)
        save(ROOT/('TERMINAL-BEFORE-TRANSPORT-'+stamp+'.json'),{'allocated_bytes':size,'largest_file_bytes':largest,'free_bytes':free,'available_memory_bytes':mem,'limit_event':reason})
    except Exception as ex:reason='TERMINAL_PRETRANSPORT_ACCOUNTING_EXCEPTION: '+repr(ex)
    try:compress_completed(ROOT,force=True)
    except Exception as ex:reason="TRACE_TRANSPORT_FAILURE: "+repr(ex)
    try:
        size,largest=allocated(ROOT);peak=max(peak,size)
        free=min(shutil.disk_usage(ROOT).free,shutil.disk_usage(args.backing_store).free);lowfree=min(lowfree,free)
        mem=available();lowmem=min(lowmem,mem)
        reason=reason or limit_event(size,largest,free,mem,cap,floor,perfile)
    except Exception as ex:reason='TERMINAL_ACCOUNTING_EXCEPTION: '+repr(ex)
    receipt={'status':'TERMINAL_EXIT_ZERO' if rc==0 and reason is None else 'TERMINAL_FAILED_OR_GUARDED_STOP','exit_code':rc,'limit_event':reason,'elapsed_seconds':time.monotonic()-t,'peak_path_counted_allocated_bytes':peak,'minimum_observed_free_bytes':lowfree,'minimum_observed_available_memory_bytes':lowmem,'poll_seconds':2,'allocation_limit_bytes':cap,'per_file_hard_limit_bytes':perfile,'free_floor_bytes':floor,'stdout':stdout.name,'stderr':stderr.name,'unchanged_core_sha256':prep['scripts']['build_connected.py'],'compiler_flags_caps_sources_and_audit_unchanged':True,'originals_and_failed_logs_preserved':True}
    save(ROOT/('SUPERVISOR-'+stamp+'.json'),receipt)
    print(json.dumps(receipt),flush=True)
    return 0 if rc==0 and reason is None else 1
if __name__=='__main__':raise SystemExit(main())
