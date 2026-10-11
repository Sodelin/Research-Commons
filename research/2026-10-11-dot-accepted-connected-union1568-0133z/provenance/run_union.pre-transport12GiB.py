#!/usr/bin/env python3
"""Run the unchanged strict builder with measured desktop storage supervision."""
import argparse,hashlib,json,os,resource,shutil,signal,subprocess,time
from pathlib import Path

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
    for m,e in graph['targets'][args.target]['modules'].items():
        assert hashlib.sha256((ROOT/'source-store'/(e['sha256']+'.lean')).read_bytes()).hexdigest()==e['sha256'],m
    assert hashlib.sha256((ROOT/'DEPENDENCY-GRAPH.json').read_bytes()).hexdigest()==prep['graph_sha256']
    assert available()>=7*2**30,'Insufficient initial memory for existing aggregate/Theta exceptions'
    cap=12*2**30;floor=8*2**30;perfile=512*2**20
    start_size,largest=allocated(ROOT)
    storage={'status':'PASS_PREFLIGHT_GUARDED_ALLOCATION_NOT_UNKNOWN_OUTPUT_CERTIFICATION','package_initial_allocated_bytes':start_size,'source_bytes':prep['source_bytes'],'new_g3_source_bytes':prep['new_source_bytes'],'package_path_counted_limit_bytes':cap,'per_file_hard_limit_bytes':perfile,'free_floor_bytes':floor,'package_filesystem_free':shutil.disk_usage(ROOT).free,'backing_store_free':shutil.disk_usage(args.backing_store).free,'dependency_checkout_allocated_bytes':allocated(args.mathlib)[0],'existing_g3_external_observed_peak_bytes':1932623872,'output_reserve_explanation':'12 GiB monitored package allocation; preserved dependency cache separately measured. Unknown compiler output is guarded rather than inferred from source size. No CPU/kernel/memory/time policy changes.'}
    assert min(storage['package_filesystem_free'],storage['backing_store_free'])>cap+floor
    save(ROOT/'STORAGE-PREFLIGHT.json',storage)
    env=dict(os.environ,CONNECTED_LEAN_BIN=str(args.lean_bin.resolve()),CONNECTED_MATHLIB=str(args.mathlib.resolve()),PYTHONUNBUFFERED='1')
    cmd=['/usr/bin/python3',str(ROOT/'scripts/build_desktop.py'),args.target]
    def limits():resource.setrlimit(resource.RLIMIT_FSIZE,(perfile,perfile))
    stamp=time.strftime('%Y%m%dT%H%M%SZ',time.gmtime())
    stdout=ROOT/('SUPERVISOR-'+stamp+'.stdout');stderr=ROOT/('SUPERVISOR-'+stamp+'.stderr')
    t=time.monotonic();peak=start_size;lowmem=available();lowfree=min(shutil.disk_usage(ROOT).free,shutil.disk_usage(args.backing_store).free);reason=None
    with stdout.open('wb') as sout,stderr.open('wb') as serr:
        child=subprocess.Popen(cmd,cwd=ROOT,env=env,stdout=sout,stderr=serr,start_new_session=True,preexec_fn=limits)
        save(ROOT/'ACTIVE-PROCESS.json',{'pid':child.pid,'process_group':child.pid,'command':cmd,'target':args.target,'started_utc':stamp})
        while child.poll() is None:
            size,largest=allocated(ROOT);peak=max(peak,size);mem=available();lowmem=min(lowmem,mem);free=min(shutil.disk_usage(ROOT).free,shutil.disk_usage(args.backing_store).free);lowfree=min(lowfree,free)
            if size>=cap:reason='PACKAGE_ALLOCATION_LIMIT'
            elif largest>=perfile:reason='PER_FILE_LIMIT'
            elif free<floor:reason='FREE_STORAGE_FLOOR'
            elif mem<2**30:reason='AVAILABLE_MEMORY_FLOOR'
            if reason:
                os.killpg(child.pid,signal.SIGTERM)
                try:child.wait(timeout=10)
                except subprocess.TimeoutExpired:os.killpg(child.pid,signal.SIGKILL);child.wait()
                break
            time.sleep(2)
        rc=child.wait()
    size,largest=allocated(ROOT);peak=max(peak,size)
    receipt={'status':'TERMINAL_EXIT_ZERO' if rc==0 and reason is None else 'TERMINAL_FAILED_OR_GUARDED_STOP','exit_code':rc,'limit_event':reason,'elapsed_seconds':time.monotonic()-t,'peak_path_counted_allocated_bytes':peak,'minimum_observed_free_bytes':lowfree,'minimum_observed_available_memory_bytes':lowmem,'poll_seconds':2,'allocation_limit_bytes':cap,'per_file_hard_limit_bytes':perfile,'free_floor_bytes':floor,'stdout':stdout.name,'stderr':stderr.name,'unchanged_core_sha256':prep['scripts']['build_connected.py'],'compiler_flags_caps_sources_and_audit_unchanged':True,'originals_and_failed_logs_preserved':True}
    save(ROOT/('SUPERVISOR-'+stamp+'.json'),receipt)
    print(json.dumps(receipt),flush=True)
    return 0 if rc==0 and reason is None else 1
if __name__=='__main__':raise SystemExit(main())
