#!/usr/bin/env python3
"""Private fixed-input selected-prefix validation guard; SOURCE-ONLY until scheduled.

Contributor: Codex rust_implementation, 2026-10-11. This guard is Linux-specific.
The --execute-approved switch acknowledges the external root/sole-scheduler gate;
it is not an authentication or permission mechanism. No automatic Cargo/core/deps
rebuild or alternative target is allowed. It records bounded process evidence,
not a native/Lean refinement or source-admission certificate.
"""
from __future__ import annotations
import argparse,ctypes,datetime,hashlib,json,os,re,resource,selectors,signal,subprocess,sys,time
from pathlib import Path

SCRATCH_HARD=2*1024**3
SCRATCH_ABORT=2013265920
MEMORY_HARD=16*1024**3
MEMORY_ABORT=15*1024**3
OUTPUT_RESERVE=32*1024**2
LOG_CAP=1024**2
SAMPLE_CAP=1024**2
FILE_CAP=16*1024**2
COUNTED_WORK=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
PLAN_SHA='5b4c8d582187573b1f86e623c764b03ed65b79050adc4fcae108ab11d269ca73'
EXPECTED_CANDIDATE='46172afa3ba29b19ea924a4110be822104ca236566a69d8d91e5170a0b6d7af3'
EXPECTED_HARNESS='629bf07a76958e099e7e04343bcb6f2f0ffa682c18a638721a48dc1004200795'

class Refusal(RuntimeError):pass

def stamp():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def digest(path):
    p=Path(path);h=hashlib.sha256()
    with p.open('rb') as stream:
        for chunk in iter(lambda:stream.read(1<<20),b''):h.update(chunk)
    return {'path':str(p),'bytes':p.stat().st_size,'sha256':h.hexdigest()}
def authenticate(row):
    observed=digest(row['path'])
    if observed!=row:raise Refusal('INPUT_PIN_MISMATCH:'+row['path'])
    return observed

def save_new(path,data,cap=1<<20):
    raw=(json.dumps(data,sort_keys=True,indent=2)+'\n').encode('ascii')
    if len(raw)>cap:raise Refusal('GUARD_METADATA_CAP')
    with Path(path).open('xb') as stream:stream.write(raw)

def allocated(roots):
    """Same distinct-inode lstat/st_blocks accounting as the pinned producer guard.
    Directory symlink targets are not traversed; all fixed counted roots must be
    supplied by the authenticated current producer plan. Missing roots refuse.
    """
    seen=set();total=0
    for root in roots:
        if not Path(root).is_dir():raise Refusal('COUNTED_ROOT_MISSING:'+root)
        for directory,dirs,files in os.walk(root,followlinks=False):
            for path in [Path(directory),*(Path(directory)/name for name in files)]:
                try:st=path.lstat()
                except FileNotFoundError:continue
                key=(st.st_dev,st.st_ino)
                if key not in seen:seen.add(key);total+=st.st_blocks*512
    return total

def memory():
    values=dict(line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
    chosen={key:int(values[key]) for key in ('anon','shmem','kernel')}
    chosen['nonreclaimable_estimate']=sum(chosen.values())
    chosen['memory_current_informational_only']=int(Path('/sys/fs/cgroup/memory.current').read_text())
    return chosen

def active_markers(roots,own=None):
    return [str(Path(root)/'ACTIVE-GUARDED-PROCESS.json') for root in roots
            if (Path(root)/'ACTIVE-GUARDED-PROCESS.json').exists()
            and Path(root)/'ACTIVE-GUARDED-PROCESS.json'!=own]

def measurements(roots,out=None):
    return {'memory':memory(),'global_distinct_inode_allocated_bytes':allocated(roots),
            'fresh_output_allocated_bytes':allocated([str(out)]) if out is not None else 0}

def limit_reason(measured):
    m=measured['memory']['nonreclaimable_estimate'];s=measured['global_distinct_inode_allocated_bytes']
    if m>=MEMORY_HARD:return 'GLOBAL_NONRECLAIMABLE_MEMORY_HARD_LIMIT'
    if m>=MEMORY_ABORT:return 'GLOBAL_NONRECLAIMABLE_MEMORY_ABORT'
    if s>=SCRATCH_HARD:return 'GLOBAL_SCRATCH_HARD_LIMIT'
    if s>=SCRATCH_ABORT:return 'GLOBAL_SCRATCH_ABORT_WITH_HEADROOM'
    if measured['fresh_output_allocated_bytes']>=OUTPUT_RESERVE:return 'FRESH_OUTPUT32MIB_LIMIT'
    return None

def proc_rows():
    rows={}
    for entry in Path('/proc').iterdir():
        if not entry.name.isdigit():continue
        try:
            raw=(entry/'stat').read_text();parts=raw[raw.rfind(')')+2:].split()
            rows[int(entry.name)]=(int(parts[1]),int(parts[19]))
        except (OSError,ValueError,IndexError):continue
    return rows

def remember_descendants(leader,known):
    rows=proc_rows();parents={leader,os.getpid()}
    # Subreaper-adopted descendants of this one serial child are also retained.
    parents.update(pid for pid,birth in known.items() if pid in rows and rows[pid][1]==birth)
    changed=True
    while changed:
        changed=False
        for pid,(ppid,birth) in rows.items():
            if ppid in parents and pid!=os.getpid() and pid not in known:
                known[pid]=birth;parents.add(pid);changed=True
    return rows

def alive(known):
    rows=proc_rows()
    return [pid for pid,birth in known.items() if pid in rows and rows[pid][1]==birth]

def signal_known(known,sig):
    for pid in alive(known):
        try:os.kill(pid,sig)
        except ProcessLookupError:pass

def become_subreaper():
    # Reap detached compiler descendants as well as the direct leader.
    if not sys.platform.startswith('linux'):raise Refusal('LINUX_PROC_SUBREAPER_REQUIRED')
    libc=ctypes.CDLL(None,use_errno=True)
    libc.prctl.argtypes=[ctypes.c_int,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong,ctypes.c_ulong]
    libc.prctl.restype=ctypes.c_int
    if libc.prctl(36,1,0,0,0)!=0:raise Refusal('SUBREAPER_SETUP:'+str(ctypes.get_errno()))

def stop_and_reap(child,known):
    """Freeze known processes, discover stopped descendants, kill and reap.
    PID birth identities reduce PID-reuse hazards. This is Linux /proc cleanup,
    not a portable or adversarial-process-completeness claim.
    """
    remember_descendants(child.pid,known)
    live_before=alive(known)
    try:os.killpg(child.pid,signal.SIGSTOP)
    except ProcessLookupError:pass
    signal_known(known,signal.SIGSTOP)
    for _ in range(3):
        remember_descendants(child.pid,known);signal_known(known,signal.SIGSTOP)
    try:os.killpg(child.pid,signal.SIGKILL)
    except ProcessLookupError:pass
    signal_known(known,signal.SIGKILL)
    rc=child.wait(timeout=5)
    reaped=[];deadline=time.monotonic()+5
    while time.monotonic()<deadline:
        progress=False
        for pid in list(known):
            if pid==child.pid:continue
            try:found,status=os.waitpid(pid,os.WNOHANG)
            except ChildProcessError:continue
            if found:reaped.append({'pid':found,'wait_status':status});progress=True
        survivors=alive(known)
        if not survivors:break
        signal_known(known,signal.SIGKILL)
        if not progress:time.sleep(0.02)
    return {'leader_exit_code':rc,'known_processes':len(known),'live_before_cleanup':live_before,
            'reaped_adopted_descendants':reaped,'survivors':alive(known)}

def child_caps(address_space,wall):
    def apply():
        resource.setrlimit(resource.RLIMIT_AS,(address_space,address_space))
        resource.setrlimit(resource.RLIMIT_CPU,(wall+5,wall+5))
        resource.setrlimit(resource.RLIMIT_FSIZE,(FILE_CAP,FILE_CAP))
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    return apply

def authenticate_all(cfg):
    return [authenticate(row) for row in cfg['input_pins']]

def run_step(name,argv,address_space,wall,env,cfg,out,marker,events,generated=None):
    stepdir=out/name;stepdir.mkdir(exist_ok=False)
    before=measurements(cfg['allocation_roots'],out)
    if limit_reason(before):raise Refusal('PRE_STEP_'+limit_reason(before))
    if active_markers(cfg['allocation_roots'],marker):raise Refusal('FOREIGN_ACTIVE_PRODUCER')
    authenticate_all(cfg)
    if generated is not None:authenticate(generated)
    streams={};selector=selectors.DefaultSelector();known={};child=None
    reason=None;error=None;cleanup=None;started_utc=stamp();started=time.monotonic();last=before
    peak_global=before['global_distinct_inode_allocated_bytes'];peak_mem=before['memory']['nonreclaimable_estimate'];peak_fresh=before['fresh_output_allocated_bytes']
    logs={kind:{'captured':0,'observed':0,'truncated':False} for kind in ('stdout','stderr')}
    sample_bytes=0;next_sample=started;next_measure=started;next_tree=started;ended_at=None
    try:
        for kind in logs:streams[kind]=(stepdir/(kind+'.txt')).open('xb')
        samples=(stepdir/'resources.jsonl').open('xb')
        try:
            child=subprocess.Popen(argv,cwd=out,env=env,stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True,
                preexec_fn=child_caps(address_space,wall))
            events[name]={'child_started':True,'pid':child.pid,'started_utc':stamp()}
            remember_descendants(child.pid,known)
            for kind,pipe in [('stdout',child.stdout),('stderr',child.stderr)]:
                os.set_blocking(pipe.fileno(),False);selector.register(pipe,selectors.EVENT_READ,kind)
            while child.poll() is None or selector.get_map():
                now=time.monotonic()
                if now>=next_measure:
                    last=measurements(cfg['allocation_roots'],out);next_measure=now+0.5
                    peak_global=max(peak_global,last['global_distinct_inode_allocated_bytes'])
                    peak_mem=max(peak_mem,last['memory']['nonreclaimable_estimate']);peak_fresh=max(peak_fresh,last['fresh_output_allocated_bytes'])
                    reason=reason or limit_reason(last)
                    if active_markers(cfg['allocation_roots'],marker):reason=reason or 'FOREIGN_ACTIVE_PRODUCER_DURING_RUN'
                if now>=next_tree:remember_descendants(child.pid,known);next_tree=now+0.25
                if now>=next_sample:
                    raw=(json.dumps({'elapsed_seconds':round(now-started,3),**last},sort_keys=True)+'\n').encode()
                    if sample_bytes+len(raw)>SAMPLE_CAP:reason=reason or 'RESOURCE_SAMPLE_LOG_CAP'
                    else:samples.write(raw);samples.flush();sample_bytes+=len(raw)
                    next_sample=now+0.5
                if now-started>=wall:reason=reason or 'WALL_TIMEOUT'
                if reason and cleanup is None:cleanup=stop_and_reap(child,known)
                if child.poll() is not None and ended_at is None:
                    ended_at=now
                    if cleanup is None:
                        remember_descendants(child.pid,known)
                        leaked=[pid for pid in alive(known) if pid!=child.pid]
                        if leaked:reason=reason or 'DESCENDANT_SURVIVED_LEADER'
                        cleanup=stop_and_reap(child,known)
                if ended_at is not None and now-ended_at>5 and selector.get_map():
                    reason=reason or 'PIPE_DRAIN_TIMEOUT';break
                for key,_ in selector.select(timeout=0.1):
                    pipe=key.fileobj;kind=key.data
                    try:chunk=os.read(pipe.fileno(),65536)
                    except BlockingIOError:continue
                    if not chunk:selector.unregister(pipe);pipe.close();continue
                    row=logs[kind];row['observed']+=len(chunk)
                    keep=min(len(chunk),LOG_CAP-row['captured'])
                    if keep:streams[kind].write(chunk[:keep]);streams[kind].flush();row['captured']+=keep
                    if keep<len(chunk):row['truncated']=True;reason=reason or kind.upper()+'_LOG_CAP'
            rc=child.wait(timeout=5)
        finally:samples.close()
    except BaseException as exc:
        reason=reason or 'GUARD_OR_EXECUTION_EXCEPTION';error=repr(exc);rc=None
    finally:
        if child is not None:
            try:
                if cleanup is None or child.poll() is None or alive(known):cleanup=stop_and_reap(child,known)
                rc=child.wait(timeout=5)
                if cleanup['survivors']:reason=reason or 'DESCENDANT_CLEANUP_INCOMPLETE'
            except BaseException as exc:reason=reason or 'DESCENDANT_CLEANUP_EXCEPTION';error=repr(exc)
        for key in list(selector.get_map().values()):
            try:key.fileobj.close()
            except OSError:pass
        selector.close()
        for stream in streams.values():stream.close()
    after=measurements(cfg['allocation_roots'],out)
    reason=reason or limit_reason(after)
    stable=False
    try:
        authenticate_all(cfg)
        if generated is not None:authenticate(generated)
        stable=True
    except BaseException as exc:reason=reason or 'POST_STEP_PIN_DRIFT';error=repr(exc)
    peak_global=max(peak_global,after['global_distinct_inode_allocated_bytes']);peak_mem=max(peak_mem,after['memory']['nonreclaimable_estimate']);peak_fresh=max(peak_fresh,after['fresh_output_allocated_bytes'])
    result={'schema':'private_selected_prefix_guarded_step_v1','name':name,
        'status':'PASS_PROCESS_EXIT_ZERO' if rc==0 and reason is None else 'PRESERVED_FAILED_OR_RESOURCE_ABORTED',
        'command_argv':argv,'exit_code':rc,'child_started':child is not None,'started_utc':started_utc,
        'elapsed_seconds':time.monotonic()-started,'abort_reason':reason,'error':error,'cleanup':cleanup,
        'before':before,'after':after,'peak_global_allocated_bytes':peak_global,'peak_nonreclaimable_estimate_bytes':peak_mem,
        'peak_fresh_output_allocated_bytes':peak_fresh,'input_pins_stable':stable,
        'streams':{kind:{**value,'capture':digest(stepdir/(kind+'.txt')),
                   'observed_bytes_are_lower_bound_if_truncated':value['truncated']} for kind,value in logs.items()},
        'address_space_limit_bytes':address_space,'wall_limit_seconds':wall,'log_cap_per_stream_bytes':LOG_CAP,
        'captured_input_pins_stable':stable,'source_or_dependency_edits_performed_by_guard':False,'mathematical_or_refinement_certificate':False}
    save_new(stepdir/'RECEIPT.json',result)
    return result

def load_config(args):
    if len(args.expected_config_sha256)!=64:raise Refusal('CONFIG_SHA')
    if digest(args.config)['sha256']!=args.expected_config_sha256:raise Refusal('CONFIG_PIN')
    raw=args.config.read_bytes()
    if len(raw)>1<<20:raise Refusal('CONFIG_BYTES')
    cfg=json.loads(raw)
    authenticate(cfg['helper_pin']);authenticate(cfg['plan_pin']);authenticate(cfg['current_producer_plan_pin'])
    if Path(cfg['helper_pin']['path']).resolve()!=Path(__file__).resolve():raise Refusal('HELPER_PATH')
    if cfg['plan_pin']['sha256']!=PLAN_SHA:raise Refusal('PLAN_SCOPE')
    plan=json.loads(Path(cfg['plan_pin']['path']).read_bytes())
    producer=json.loads(Path(cfg['current_producer_plan_pin']['path']).read_bytes())
    if cfg['allocation_roots']!=producer['allocation_roots']:raise Refusal('CURRENT_ROOT_LIST')
    previous=json.loads((COUNTED_WORK/'RESOURCE-AND-RUN-PLAN.json').read_bytes())
    if not set(previous['allocation_roots']).issubset(cfg['allocation_roots']):raise Refusal('PRIOR_ROOT_OMISSION')
    if str(COUNTED_WORK) not in cfg['allocation_roots']:raise Refusal('OUTPUT_ROOT_UNCOUNTED')
    if len(plan['inputs'])!=18 or cfg['input_pins'][:18]!=plan['inputs']:raise Refusal('FROZEN18INPUTS')
    if cfg['expected_test_names']!=[case['name'] for case in plan['cases']]:raise Refusal('FROZEN_FIVE_TEST_HEADS')
    if plan['inputs'][0]['sha256']!=EXPECTED_CANDIDATE or plan['inputs'][4]['sha256']!=EXPECTED_HARNESS:raise Refusal('FROZEN_SOURCE_SCOPE')
    if cfg['compile_argv']!=plan['preferred_build']['command_argv'] or cfg['runtime_argv']!=plan['runtime']['command_argv']:raise Refusal('EXACT_COMMAND_DRIFT')
    if cfg['scratch_hard_bytes']!=SCRATCH_HARD or cfg['scratch_abort_bytes']!=SCRATCH_ABORT or cfg['memory_hard_bytes']!=MEMORY_HARD or cfg['memory_abort_bytes']!=MEMORY_ABORT:raise Refusal('GLOBAL_LIMIT_DRIFT')
    if cfg['fresh_output_reserve_bytes']!=OUTPUT_RESERVE or cfg['log_cap_per_stream_bytes']!=LOG_CAP:raise Refusal('OUTPUT_LIMIT_DRIFT')
    if producer['scratch_hard_limit_bytes']!=SCRATCH_HARD or producer['scratch_abort_bytes']!=SCRATCH_ABORT or producer['memory_abort_bytes']!=MEMORY_ABORT:raise Refusal('PRODUCER_LIMIT_DRIFT')
    out=Path(cfg['output_directory'])
    expected=Path(plan['preferred_build']['output']).parent
    if out!=expected or not out.is_relative_to(COUNTED_WORK/'metadata'):raise Refusal('FIXED_OUTPUT_PATH')
    if cfg['compile_argv'][0]!=plan['inputs'][12]['path'] or cfg['runtime_argv'][0]!=plan['preferred_build']['output']:raise Refusal('TARGET_SCOPE')
    if 'cargo' in Path(cfg['compile_argv'][0]).name:raise Refusal('NO_CARGO_REBUILD')
    authenticate_all(cfg)
    return cfg,plan,out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--config',required=True,type=Path)
    parser.add_argument('--expected-config-sha256',required=True)
    parser.add_argument('--execute-approved',action='store_true')
    args=parser.parse_args()
    if not args.execute_approved:raise Refusal('EXTERNAL_ROOT_SCHEDULER_GATE_NOT_ACKNOWLEDGED')
    cfg,plan,out=load_config(args)
    if out.exists():raise Refusal('CREATE_NEW_OUTPUT_REQUIRED')
    if active_markers(cfg['allocation_roots']):raise Refusal('ACTIVE_PRODUCER_BEFORE_LAUNCH')
    initial=measurements(cfg['allocation_roots'])
    reason=limit_reason(initial)
    if reason:raise Refusal('PRELAUNCH_'+reason)
    if initial['global_distinct_inode_allocated_bytes']+OUTPUT_RESERVE>=SCRATCH_ABORT:raise Refusal('PRELAUNCH32MIB_RESERVE_NOT_AVAILABLE')
    become_subreaper()
    marker=COUNTED_WORK/'ACTIVE-GUARDED-PROCESS.json';marker_bytes=(json.dumps({'pid':os.getpid(),'phase':'private-selected-prefix','output':str(out)},sort_keys=True)+'\n').encode()
    fd=os.open(marker,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
    with os.fdopen(fd,'wb') as stream:stream.write(marker_bytes)
    steps=[];events={};out_created=False;error=None;binary_pin=None;started=stamp()
    try:
        if active_markers(cfg['allocation_roots'],marker):raise Refusal('FOREIGN_ACTIVE_PRODUCER_AFTER_SERIAL_MARKER')
        out.mkdir(mode=0o700,exist_ok=False);out_created=True;(out/'tmp').mkdir(exist_ok=False)
        env=dict(os.environ);env.update(plan['preferred_build']['environment'])
        env['PYTHONDONTWRITEBYTECODE']='1';env['CARGO_INCREMENTAL']='0'
        save_new(out/'PRE-RUN-PINS.json',{'checked':authenticate_all(cfg),'config':digest(args.config),'helper':digest(__file__),
                                       'producer_plan':cfg['current_producer_plan_pin'],'initial':initial})
        compile_step=run_step('compile',cfg['compile_argv'],2*1024**3,120,env,cfg,out,marker,events)
        steps.append(compile_step)
        if compile_step['status']=='PASS_PROCESS_EXIT_ZERO':
            binary_pin=digest(plan['preferred_build']['output'])
            steps.append(run_step('tests',cfg['runtime_argv'],512*1024**2,120,env,cfg,out,marker,events,binary_pin))
    except BaseException as exc:error=repr(exc)
    finally:
        try:
            if marker.read_bytes()==marker_bytes:marker.unlink()
            else:error=error or 'SERIAL_MARKER_CHANGED_NOT_REMOVED'
        except BaseException as exc:error=error or repr(exc)
    passed=error is None and len(steps)==2 and all(step['status']=='PASS_PROCESS_EXIT_ZERO' for step in steps)
    final=measurements(cfg['allocation_roots'],out if out_created else None)
    if limit_reason(final):passed=False;error=error or 'FINAL_'+limit_reason(final)
    test_summary_checked=False
    if passed:
        try:
            raw=(out/'tests/stdout.txt').read_bytes()
            if len(raw)>LOG_CAP:raise Refusal('TEST_SUMMARY_CAPTURE_CAP')
            report=raw.decode('utf-8')
            if not re.search(r'(?m)^running 5 tests$',report):raise Refusal('FIVE_TEST_COUNT_NOT_OBSERVED')
            if not re.search(r'test result: ok[.] 5 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;',report):
                raise Refusal('FIVE_TEST_SUCCESS_NOT_OBSERVED')
            for name in cfg['expected_test_names']:
                if not re.search(r'(?m)^test '+re.escape(name)+r' [.][.][.] ok$',report):
                    raise Refusal('TEST_HEAD_NOT_OBSERVED:'+name)
            test_summary_checked=True
        except BaseException as exc:passed=False;error=error or repr(exc)
    final_pins=[]
    try:final_pins=authenticate_all(cfg)
    except BaseException as exc:passed=False;error=error or repr(exc)
    result={'schema':'private_selected_prefix_validation_execution_v1','status':'PASS_FIVE_TARGETED_TESTS' if passed else 'PRESERVED_FAILED_OR_RESOURCE_ABORTED',
            'started_utc':started,'ended_utc':stamp(),'helper':digest(__file__),'config':digest(args.config),
            'compiler_called':bool(events.get('compile',{}).get('child_started')),'test_binary_called':bool(events.get('tests',{}).get('child_started')),
            'actual_launch_events':events,
            'steps':steps,'error':error,'private_binary':binary_pin,'initial':initial,'final':final,
            'exact_five_test_stdout_summary_checked':test_summary_checked,
            'final_authenticated_input_pins':final_pins,'unchanged_public_crate_or_native_binary_executed':False,
            'cargo_or_dependencies_rebuilt':False,'old_elf_or_rlib_copied':False,
            'source_admission_verified':False,'native_lean_refinement_verified':False,'compiler_literal_order_verified':False,
            'literal_code_history_verified':False,'timed_merger_history_supported':False,
            'independence_claimed':False,'new_G6_factorization_acceptance_claimed':False}
    if out_created:save_new(out/'RESULT.json',result)
    print(json.dumps({'status':result['status'],'output':str(out),'result_written':out_created,'error':error},sort_keys=True))
    return 0 if passed else 1

if __name__=='__main__':
    try:raise SystemExit(main())
    except (Refusal,OSError,ValueError,KeyError) as exc:
        print(json.dumps({'status':'REFUSED_BEFORE_OR_OUTSIDE_TARGET_EXECUTION','error':str(exc)},sort_keys=True),file=sys.stderr)
        raise SystemExit(1)
