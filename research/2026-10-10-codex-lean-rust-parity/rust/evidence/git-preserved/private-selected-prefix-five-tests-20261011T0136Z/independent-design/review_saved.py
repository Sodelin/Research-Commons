#!/usr/bin/env python3
"""Own saved result/byte reader only; target code, guards and binaries never run."""
from datetime import datetime,timezone
from pathlib import Path
import hashlib,json,re,sys
W=Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
M=W/'metadata/selected-prefix-validation-sourceonly-20261011T0054Z'
G=M/'source-only-execution-guard-20261011T0112Z'
R=M/'execution-1'
def require(ok,why):
    if not ok:raise AssertionError(why)
def hash_file(p):
    h=hashlib.sha256()
    with Path(p).open('rb') as f:
        for block in iter(lambda:f.read(65536),b''):h.update(block)
    return h.hexdigest()
def pin(row):
    p=Path(row['path']);require(p.stat().st_size==row['bytes'] and hash_file(p)==row['sha256'],'saved byte pin '+str(p));return row
def load(p,h=None):
    p=Path(p);row={'path':str(p),'bytes':p.stat().st_size,'sha256':hash_file(p)};require(h is None or row['sha256']==h,'fixed main receipt pin '+str(p));return row,json.loads(p.read_bytes())
def check():
    result_pin,result=load(R/'RESULT.json','819c426888e1da6d798d169d81ac6f43eb14a6135076f77497d7de85f7a91b64')
    owner_pin,owner=load(G/'ACTUAL-SLOT-SAVED-OWNER-BINDINGS-20261011T012245Z.json','d7b8fbe9f5e25ef759fd318e258b09f1d571e7f01678b726be7c938a0a2a10e9')
    config_pin=pin(result['config']);require(config_pin==owner['config'] and config_pin['sha256']=='67a54737ab68b50a2585a149d73f6b637f7ead8d5f129f16fffab429089ef73d','exact actual V4 config')
    config=json.loads(Path(config_pin['path']).read_bytes());plan_pin=pin(config['plan_pin']);plan=json.loads(Path(plan_pin['path']).read_bytes());producer_pin=pin(config['current_producer_plan_pin']);producer=json.loads(Path(producer_pin['path']).read_bytes())
    require(producer_pin['sha256']=='0db1bb265fec8e2a4c89b0361d2b48f3f38c17d35aeb479b623c0954f097bac5' and config['allocation_roots']==producer['allocation_roots'] and len(config['allocation_roots'])==25,'exact actual25-root state')
    require(result['status']=='PASS_FIVE_TARGETED_TESTS' and result['error'] is None and result['compiler_called'] and result['test_binary_called'],'actual private compile and test result')
    require(result['helper']==owner['helper']==config['helper_pin'] and pin(result['helper'])['sha256']=='01c20a0e3ecf34634814e74645122bcf5945b411168531dcbb92717e54ba6e3d','unchanged accepted guard source')
    pin(owner['freeze']);require(owner['freeze']['sha256']=='a945edf3f4d996b402cbc97506964859b49d27ff251365d3d7054c75bc7b3fa9','frozen V4 source binding')
    require(config['input_pins']==result['final_authenticated_input_pins']==owner['input_pins'] and len(config['input_pins'])==43 and len({r['path'] for r in config['input_pins']})==43,'all43 distinct pre/post input identities')
    inputs=[pin(r) for r in config['input_pins']]
    pre_pin,pre=load(R/'PRE-RUN-PINS.json');require(pre['checked']==inputs and pre['config']==config_pin and pre['helper']==result['helper'],'actual pre-run inputs agree final/current')
    inventory=owner['private_output_files'];require({r['path'] for r in inventory}=={str(p) for p in R.rglob('*') if p.is_file()},'complete saved private output file inventory')
    checked_outputs=[pin(r) for r in inventory];outer=[pin(r) for r in owner['outer_launch_files']]
    launch=json.loads((G/'ACTUAL-EXCLUSIVE-SLOT-1.LAUNCH.json').read_bytes());terminal=json.loads((G/'ACTUAL-EXCLUSIVE-SLOT-1.TERMINAL.json').read_bytes());approval_pin=pin(launch['approval']);approval=json.loads(Path(approval_pin['path']).read_bytes())
    require(approval_pin['sha256']=='74ffc3edc127dcfeac277413d841dbbe484dc2bef0a90f3f73cc18695eb0e135' and terminal['approval']==approval_pin,'exact root once-only serial approval')
    require(launch['argv']==terminal['argv']==approval['command_argv'] and terminal['guard_exit_code']==0 and terminal['guard_not_retried'],'exact launch/terminal binding/no rerun')
    require(terminal['actual_phase_details_path']==str(R/'RESULT.json') and result['ended_utc']<=terminal['observed_utc'],'phase result precedes terminal')
    require(config['compile_argv']==plan['compile_argv'] and config['runtime_argv']==plan['runtime_argv'],'actual derivative retains exact planned argv')
    require(config['scratch_hard_bytes']==2147483648 and config['scratch_abort_bytes']==2013265920 and config['memory_hard_bytes']==17179869184 and config['memory_abort_bytes']==16106127360 and config['fresh_output_reserve_bytes']==33554432,'unchanged global resource gates')
    require(config['compile_address_space_bytes']==2147483648 and config['runtime_address_space_bytes']==536870912 and config['compile_wall_seconds']==config['runtime_wall_seconds']==120 and config['log_cap_per_stream_bytes']==1048576,'unchanged phase caps')
    require(len(result['steps'])==2 and [r['name'] for r in result['steps']]==['compile','tests'],'exact one compile and one runtime process step')
    all_samples=[];step_pins=[]
    for step in result['steps']:
        phase=step['name'];receipt_pin,saved=load(R/phase/'RECEIPT.json');require(saved==step,'phase receipt full equality')
        require(step['command_argv']==config[('compile' if phase=='compile' else 'runtime')+'_argv'],'exact phase command')
        require(step['exit_code']==step['cleanup']['leader_exit_code']==0 and step['abort_reason'] is None and step['error'] is None and step['cleanup']['survivors']==[] and step['cleanup']['live_before_cleanup']==[],'complete successful child cleanup/reap')
        require(step['input_pins_stable'] and step['captured_input_pins_stable'] and not step['mathematical_or_refinement_certificate'],'successful binding without theorem claim')
        require(step['wall_limit_seconds']==120 and step['log_cap_per_stream_bytes']==1048576 and step['address_space_limit_bytes']==config[('compile' if phase=='compile' else 'runtime')+'_address_space_bytes'],'phase runtime caps bound')
        for stream in step['streams'].values():
            capture=pin(stream['capture']);require(not stream['truncated'] and stream['captured']==stream['observed']==capture['bytes']<=1048576,'complete bounded stdout/stderr capture')
        samples=[json.loads(line) for line in (R/phase/'resources.jsonl').read_text().splitlines()];require(samples,'actual saved resource samples')
        all_samples.extend(samples)
        full=[step['before'],step['after'],*samples]
        for snap in full:
            require(snap['global_distinct_inode_allocated_bytes']<2013265920 and snap['fresh_output_allocated_bytes']<=33554432 and snap['memory']['nonreclaimable_estimate']<16106127360,'all observed resource samples below fixed limits')
            require(snap['memory']['nonreclaimable_estimate']==sum(snap['memory'][k] for k in ['anon','kernel','shmem']),'exact declared nonreclaimable arithmetic')
        require(step['peak_fresh_output_allocated_bytes']==max(x['fresh_output_allocated_bytes'] for x in full) and step['peak_global_allocated_bytes']==max(x['global_distinct_inode_allocated_bytes'] for x in full) and step['peak_nonreclaimable_estimate_bytes']==max(x['memory']['nonreclaimable_estimate'] for x in full),'saved observed peak arithmetic')
        step_pins.append(receipt_pin)
    binary=pin(result['private_binary']);require(binary['sha256']=='aaa7a2d2a87b9d2ba44afd34bf4a88aea2a1c9b45e069ffc0725250d4724a63e' and Path(binary['path'])==R/'selected-prefix-tests','only created private executable identity')
    out=(R/'tests/stdout.txt').read_text();names=config['expected_test_names']
    require(len(names)==5 and set(re.findall(r'^test ([A-Za-z0-9_]+) \.\.\. ok$',out,re.M))==set(names) and 'running 5 tests' in out and 'test result: ok. 5 passed; 0 failed; 0 ignored; 0 measured; 0 filtered out;' in out,'exact five named test results/stdout')
    require((R/'compile/stdout.txt').read_bytes()==b'' and (R/'tests/stderr.txt').read_bytes()==b'','actual empty successful streams')
    warning=(R/'compile/stderr.txt').read_text();require(len(warning.encode())==997 and 'warning: 1 warning emitted' in warning and 'never used' in warning and 'error:' not in warning,'full sole unused-accessor warning retained')
    no_claims=['compiler_literal_order_verified','source_admission_verified','literal_code_history_verified','native_lean_refinement_verified','timed_merger_history_supported','independence_claimed','new_G6_factorization_acceptance_claimed','cargo_or_dependencies_rebuilt','old_elf_or_rlib_copied','old_public_command_or_executable_started']
    require(all(result[n] is False for n in no_claims) and result['private_harness_reuses_existing_accepted_library'],'precise unchanged diagnostic-only scope')
    private_pids=[terminal['guard_pid'],launch['wrapper_pid']]+[r['pid'] for r in result['actual_launch_events'].values()]
    require(all(not (Path('/proc')/str(pid)).exists() for pid in private_pids),'dated current private phase PIDs absent')
    require(not (W/'ACTIVE-GUARDED-PROCESS.json').exists(),'private counted-work serial marker absent')
    return {'status':'PASS_SAVED_PRIVATE_FIVE_TEST_BYTES_AND_SCOPE_ONLY','result':result_pin,'owner_inventory':owner_pin,'config':config_pin,'approval':approval_pin,'private_binary':binary,'input_count':43,'protected_input_pins':inputs,'saved_output_pins':checked_outputs,'saved_outer_capture_pins':outer,'phase_receipts':step_pins,'source_trial_test_names':names,'observed_root_count':25,'observed_resource_sample_count':len(all_samples),'reported_sampled_peaks':{'fresh_bytes':max(s['peak_fresh_output_allocated_bytes'] for s in result['steps']),'global_bytes':max(s['peak_global_allocated_bytes'] for s in result['steps']),'nonreclaimable_bytes':max(s['peak_nonreclaimable_estimate_bytes'] for s in result['steps'])},'observed_private_pids_absent':private_pids,'qualifications':['Own standard-library saved readers only; no guard/module/compiler/binary/reference rerun.','Five named tests on exact frozen fixtures and private harness establish bounded selected-state diagnostic behavior. They do not establish native/Lean refinement, literal Code history, literal compiled-calendar equivalence, timed merger data, source admission or G6 factorization acceptance.','Recorded process cleanup and dated current private PID/marker absence were checked. Other roots may subsequently host separately authorized serial Lean work; historical all25-marker absence is the owner terminal observation.','Memory/scratch peaks are maxima of saved half-second observations and before/after samples, not exhaustive continuous allocation measurements. memory.current remains informational.','V4 allocation_counter_scope prose retains the inherited phrase current-producer24; the authenticated actual allocation_roots, current plan, structured pins and this receipt all bind25. No executable gate or root was omitted.','The997-byte unused-accessor warning remains fully preserved; no candidate, accepted library, public executable or source edits were made by this reviewer.']}
def main():
    out=Path(sys.argv[1]);report={'schema':'private_selected_prefix_saved_design_qc_v1','contributor':'Codex / solver_design_recovery','observed_utc':datetime.now(timezone.utc).isoformat(),'reviewer_sha256':hash_file(__file__),'producer_processes_or_target_imports':0}
    try:report.update(check())
    except Exception as exc:report.update(status='FAIL_SAVED_PRIVATE_TRIAL_QC',error_type=type(exc).__name__,error=str(exc))
    with out.open('x') as f:json.dump(report,f,indent=2,sort_keys=True);f.write('\n')
    print(json.dumps({'path':str(out),'status':report['status'],'sha256':hash_file(out)}));return int(report['status'].startswith('FAIL'))
if __name__=='__main__':raise SystemExit(main())
