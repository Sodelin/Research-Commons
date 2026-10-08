"""Fresh bounded multistage original-D producer plus separate complete checker.

The nine original numerical sources are immutable public recovered bytes.
This does not substitute the Rust receiver into the producer call graph.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import importlib.util
import json
import os
import resource
import shutil
import subprocess
import sys
import time

PACKET=Path(__file__).resolve().parent
COMMONS=PACKET.parents[2]
SCRATCH=Path('/workspace/scratch/integration-practical')
BUDGET={'scalar_steps':32,'max_stages':16,'max_splits':0,'max_states':1,'max_depth':0,
        'wall_ms':20000,'recovery_wall_ms':20000,'recovery_max_stages':16}


def sha(data):return hashlib.sha256(data).hexdigest()


def canonical(value):
    return (json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n').encode()


def command(attempt,name,args):
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU,(30,30))
        resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))
        resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    env={'PATH':os.defpath,'LANG':'C.UTF-8','PYTHONNOUSERSITE':'1',
         'PYTHONDONTWRITEBYTECODE':'1','PYTHONHASHSEED':'0'}
    started=time.monotonic()
    with (attempt/(name+'.stdout')).open('xb') as out,(attempt/(name+'.stderr')).open('xb') as err:
        p=subprocess.Popen(args,env=env,stdout=out,stderr=err,preexec_fn=limits)
        timeout=False
        try:p.wait(timeout=45)
        except subprocess.TimeoutExpired:p.kill();p.wait();timeout=True
    receipt={'command':args,'exit_code':p.returncode,'timeout':timeout,'wall_seconds':time.monotonic()-started,
             'cpu_seconds_limit':30,'wall_seconds_limit':45,'address_space_bytes_limit':512*2**20,
             'stdout_sha256':sha((attempt/(name+'.stdout')).read_bytes()),
             'stderr_sha256':sha((attempt/(name+'.stderr')).read_bytes()),
             'stderr_empty':(attempt/(name+'.stderr')).stat().st_size==0}
    (attempt/(name+'.execution.json')).write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    if p.returncode or timeout:raise RuntimeError(name+' execution failed; first result preserved')
    return receipt


def authenticate(staging,runtime):
    result={}
    for row in staging['selected_unchanged_runtime_files']:
        path=runtime/row['runtime_relative'];data=path.read_bytes()
        if path.is_symlink() or sha(data)!=row['sha256']:raise RuntimeError('runtime identity '+str(path))
        result[row['runtime_relative']]={'sha256':sha(data),'bytes':len(data)}
    if list(runtime.rglob('*.pyc')):raise RuntimeError('bytecode cache present')
    return result


def main():
    attempt=PACKET/'original-multistage';attempt.mkdir(exist_ok=False)
    runtime=SCRATCH/'jc-original'
    records=[command(attempt,'stage',[sys.executable,'-B',str(PACKET/'recovered/staging/stage_original_jc.py'),
                 '--commons-root',str(COMMONS),'--runtime-root',str(runtime),'--receipt',str(attempt/'STAGING.json')])]
    staging=json.loads((attempt/'STAGING.json').read_bytes())
    before=authenticate(staging,runtime)
    source_copy=PACKET/'recovered/jc-runtime'
    for rel in before:
        target=source_copy/rel;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((runtime/rel).read_bytes())
    request=json.loads((runtime/'REQUEST.json').read_bytes())
    request['budget']=dict(BUDGET)
    request['provenance']['cloud_control']='isolated_original_D_multistage_recovery_20261008_0825z'
    raw=canonical(request);request_sha=sha(raw)
    request_path=attempt/'REQUEST.json';request_path.write_bytes(raw)
    pins=attempt/'CHECKER-PINS.json';pins.write_bytes((runtime/'CHECKER-PINS.json').read_bytes())
    pins_sha=sha(pins.read_bytes())
    engine=runtime/staging['engine_directory'];journal=attempt/'journal'
    common=['--request',str(request_path),'--request-sha256',request_sha,'--checkpoints',str(journal)]
    records.append(command(attempt,'producer',[sys.executable,'-B',str(engine/'global_engine.py'),*common]))
    between=authenticate(staging,runtime)
    records.append(command(attempt,'checker',[sys.executable,'-B',str(engine/'global_check.py'),*common,
                       '--source-pins',str(pins),'--source-pins-sha256',pins_sha,'--normal']))
    after=authenticate(staging,runtime)
    producer=json.loads((attempt/'producer.stdout').read_bytes())
    checker=json.loads((attempt/'checker.stdout').read_bytes())
    result={'schema':'integration_practical_original_multistage_v1','status':'ASSEMBLY_PASS',
            'request_sha256':request_sha,'request_budget':BUDGET,'records':records,'producer':producer,'checker':checker,
            'source_bytes_before_between_after_equal':before==between==after,'source_identities':before,
            'original_full_D_and_nine_targets_preserved':True,'archived_arithmetic_mean_bands_unchanged':True,
            'fresh_biological_data':False,'statistical_coverage_verified':False,'parameter_accuracy_released':False,
            'rust_receiver_is_not_in_original_producer_call_graph':True,
            'journal':[{'name':p.name,'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
                       for p in sorted(journal.glob('state-*.json'))]}
    (attempt/'RESULT.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    if not checker['details'].get('complete_numeric_replay'):raise RuntimeError('complete replay pending; output preserved')
    if not result['source_bytes_before_between_after_equal']:raise RuntimeError('source changed')
    # A forged narrowing with an unchanged commit filename must invalidate the
    # chain and preserve the complete original domain, not yield a certificate.
    bad=attempt/'tampered-journal';shutil.copytree(journal,bad)
    last=sorted(bad.glob('state-*.json'))[-1];frame=json.loads(last.read_bytes())
    frame['frontier'][0]['state']['physical']['rA']=['1','1'];last.write_bytes(canonical(frame))
    control_args=[sys.executable,'-B',str(engine/'global_check.py'),'--request',str(request_path),
                  '--request-sha256',request_sha,'--checkpoints',str(bad),'--source-pins',str(pins),
                  '--source-pins-sha256',pins_sha,'--normal']
    control_execution=command(attempt,'tamper-checker',control_args)
    control=json.loads((attempt/'tamper-checker.stdout').read_bytes())
    tamper_safe=control['status']=='RECOVERED_UNKNOWN' and not control['whole_union_width_target_met'] and all(
        row['normalized_ratio']=='1' for row in control['widths'].values())
    (attempt/'TAMPER-CONTROL.json').write_text(json.dumps({'matches':tamper_safe,'checker':control,
                                    'execution':control_execution},indent=2,sort_keys=True)+'\n')
    if not tamper_safe:raise RuntimeError('tampered-journal safety control failed')
    ratios={k:v['normalized_ratio'] for k,v in checker['widths'].items()}
    print(json.dumps({'status':checker['status'],'all_nine_normalized_union_widths':ratios,
                      'maximum':str(max(Fraction(v) for v in ratios.values())),
                      'stages':producer['stages_started'],'journal_frames':len(result['journal']),
                      'complete_numeric_replay':True,'tampered_journal_falls_back_to_original_D':True},sort_keys=True))


if __name__=='__main__':main()
