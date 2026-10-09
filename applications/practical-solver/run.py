#!/usr/bin/env python3
"""Run the inherited exact nine-parameter solver and independently replay its complete journal.

Python 3.10+ and a POSIX resource module suffice. No network or third-party
Python package is used. Results never issue biological accuracy or confidence.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import html
import json
import os
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
import uuid

APP = Path(__file__).resolve().parent
ROOT = APP.parents[1]
INHERITED = ROOT / 'research/2026-10-08-codex-integration-0825z/practical'
MODEL = 'fixed-six-copy-clock-jc-nine-v1'
SCHEMA = 'global-triangular-request-v1'
PHYSICAL = ('h','u','v','rA','rB','rC','rAB','rR','g')
FEATURES = ('AC1','AC2','CC1','BC1','BC2','AB1','AB2','AA1','BB1')
DOMAIN = {k: ['1/32','1/8'] if k in ('h','u','v') else ['1/6','2/3'] if k=='g' else ['1/2','6'] for k in PHYSICAL}
CAPS = {'scalar_steps':32,'max_stages':64,'max_splits':7,'max_states':8,'max_depth':3,
        'wall_ms':20000,'recovery_wall_ms':20000,'recovery_max_stages':64}
MAX_INPUT_BYTES = 64 * 1024
MAX_JOURNAL_BYTES = 64 * 1024 * 1024
MAX_FRAMES = 512
SOURCE_MANIFEST_SHA = '375641ef893ca6af8cbec518a24d20d158dc04630dca1543e109679de347fded'
EXAMPLE_SHAS = {
    'informative':'81de438bcffe5f80a7ca3fa997365b1ecf6996a3171f81a0067f58acfe428e1f',
    'finite-data':'13fc5b7a1c9f27bad24e1dd28e83a40ff554d940cba96aa5a513f116b2d486d2',
    'unsupported':'3e281d177eb5c74a5094e146cfb89a0659e05b89cd13ea7cb4177af079e093d9'}
SAVED_SHAS = {
    'informative':'29749ffc4d75654e8fd763e525cf350df8ab4f7920b0d8e4dd8277b565a2de0d',
    'finite-data':'904c968e298e0a3d49015ea2e57437fc704bd3a4e274ffe5a9391a5f6ef76cf5',
    'unsupported':'62ce3ddd1f669d37de6cc3f820055dbd14acb9ea7b5c33ec73e83d5e8a766184'}
OBSTRUCTION_SHA = '4875533e36a0584f7fcadbb45f44c9b296b9d89ef3c670eed688b2d81b983f8a'

class InputError(ValueError): pass
class SourceError(ValueError): pass

def sha(raw): return hashlib.sha256(raw).hexdigest()
def encode(obj): return (json.dumps(obj, sort_keys=True, indent=2, allow_nan=False)+'\n').encode()
def write(path,obj):
    with path.open('xb') as f: f.write(encode(obj))
def no_duplicates(pairs):
    out={}
    for key,value in pairs:
        if key in out: raise InputError('Duplicate JSON key: '+key)
        out[key]=value
    return out

def read(path, cap=MAX_INPUT_BYTES, exact=True):
    if path.is_symlink() or not path.is_file(): raise InputError('A regular nonsymlink input file is required: '+str(path))
    if path.stat().st_size > cap: raise InputError('Input exceeds '+str(cap)+' byte limit')
    raw=path.read_bytes()
    if len(raw)>cap: raise InputError('Input grew beyond byte limit')
    def reject(value): raise InputError('Exact JSON requires integers or rational strings; found '+value[:40])
    try: obj=json.loads(raw,object_pairs_hook=no_duplicates,parse_float=reject if exact else float,parse_constant=reject)
    except (json.JSONDecodeError,RecursionError) as error: raise InputError('Malformed JSON: '+str(error)) from error
    return raw,obj

def rational(value):
    if not isinstance(value,str) or len(value)>159 or not re.fullmatch(r'-?[0-9]{1,78}(?:/[0-9]{1,78})?',value):
        raise InputError('Rational endpoints must be bounded integer or p/q strings')
    try: result=Fraction(value)
    except (ZeroDivisionError,ValueError) as error: raise InputError('Invalid rational endpoint') from error
    if max(result.numerator.bit_length(),result.denominator.bit_length())>256:
        raise InputError('Rational exceeds 256-bit input limit')
    return result

def admit(request):
    if not isinstance(request,dict): raise InputError('Request must be a JSON object')
    if request.get('model') != MODEL or request.get('schema') != SCHEMA or request.get('quantity') != 'shifted_bernoulli_character_mean':
        return 'Observation/model mapping to the original solver has not been admitted.'
    expected={'schema','model','quantity','box','features','normalized_width_targets','budget','provenance'}
    if set(request)!=expected: raise InputError('Supported request requires exactly: '+', '.join(sorted(expected)))
    if request['box']!=DOMAIN or request['normalized_width_targets']!={k:'1/20' for k in PHYSICAL}:
        return 'This workflow retains the original complete nine-parameter domain and all nine 1/20 targets.'
    if not isinstance(request['features'],dict) or set(request['features'])!=set(FEATURES):
        raise InputError('Exactly nine labelled shifted-character feature intervals are required')
    for key,pair in request['features'].items():
        if not isinstance(pair,list) or len(pair)!=2: raise InputError('Feature '+key+' requires two endpoints')
        low,high=map(rational,pair)
        if not 0<=low<=high<=1: raise InputError('Feature '+key+' must satisfy 0 <= lower <= upper <= 1')
    budget=request['budget']
    if not isinstance(budget,dict) or set(budget)!=set(CAPS): raise InputError('Budget requires the documented eight fields')
    for key,cap in CAPS.items():
        if type(budget[key]) is not int or not 0<=budget[key]<=cap: raise InputError('Budget '+key+' must be an integer in [0,'+str(cap)+']')
    if budget['max_states']<1: raise InputError('Root requires max_states >= 1')
    if not isinstance(request['provenance'],dict): raise InputError('Provenance must be a JSON object')
    return None

def create_output(proposed=None):
    out=proposed.absolute() if proposed else ROOT/'runs'/('practical-'+datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:8])
    if out.exists() or out.is_symlink(): raise InputError('Output already exists; choose a new path to preserve saved results: '+str(out))
    out.mkdir(parents=True,exist_ok=False)
    return out

def identities():
    raw,manifest=read(APP/'SOURCE-IDENTITIES.json')
    if sha(raw)!=SOURCE_MANIFEST_SHA:raise SourceError('Inherited source manifest identity mismatch')
    return manifest

def stage(out):
    manifest=identities(); runtime=out/'runtime'; runtime.mkdir()
    for row in manifest['inherited_runtime_files']:
        source=ROOT/row['source']; raw,_ignore=source.read_bytes(),None
        if source.is_symlink() or sha(raw)!=row['sha256'] or len(raw)!=row['bytes']:
            raise SourceError('Inherited runtime authentication failed: '+row['source'])
        target=runtime/row['runtime_relative'];target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb') as f:f.write(raw)
        target.chmod(0o444)
    engine=runtime/manifest['engine_directory']
    pins={name:sha((engine/name).read_bytes()) for name in manifest['checker_files']}
    write(out/'CHECKER-PINS.json',pins);write(out/'SOURCE-IDENTITIES.json',manifest)
    return runtime,engine

def authenticate(out):
    manifest=identities();result={}
    for row in manifest['inherited_runtime_files']:
        path=out/'runtime'/row['runtime_relative'];raw=path.read_bytes()
        if path.is_symlink() or sha(raw)!=row['sha256'] or len(raw)!=row['bytes']: raise SourceError('Staged runtime authentication failed: '+str(path))
        result[row['runtime_relative']]={'sha256':sha(raw),'bytes':len(raw)}
    if list((out/'runtime').rglob('*.pyc')): raise SourceError('Unexpected runtime bytecode cache; use a fresh run')
    _,pins=read(out/'CHECKER-PINS.json')
    engine=out/'runtime'/manifest['engine_directory']
    if pins!={name:sha((engine/name).read_bytes()) for name in manifest['checker_files']}:
        raise SourceError('Checker source pins do not match inherited runtime')
    return result

def execute(out,name,command):
    def limits():
        resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(512*2**20,512*2**20))
        resource.setrlimit(resource.RLIMIT_FSIZE,(16*2**20,16*2**20));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
    env={'PATH':os.defpath,'LANG':'C.UTF-8','PYTHONNOUSERSITE':'1','PYTHONDONTWRITEBYTECODE':'1','PYTHONHASHSEED':'0'}
    start=time.monotonic(); before=resource.getrusage(resource.RUSAGE_CHILDREN)
    with (out/(name+'.stdout')).open('xb') as stdout,(out/(name+'.stderr')).open('xb') as stderr:
        process=subprocess.Popen(command,env=env,stdout=stdout,stderr=stderr,preexec_fn=limits)
        timeout=False
        try:process.wait(timeout=45)
        except subprocess.TimeoutExpired: process.kill();process.wait();timeout=True
    after=resource.getrusage(resource.RUSAGE_CHILDREN)
    receipt={'command':command,'exit_code':process.returncode,'timeout':timeout,'wall_seconds':time.monotonic()-start,
             'cpu_seconds':after.ru_utime+after.ru_stime-before.ru_utime-before.ru_stime,
             'cumulative_children_max_rss_kib':after.ru_maxrss,'cpu_limit_seconds':30,'wall_limit_seconds':45,
             'address_space_limit_bytes':512*2**20,'per_file_limit_bytes':16*2**20,
             'stdout_sha256':sha((out/(name+'.stdout')).read_bytes()),'stderr_sha256':sha((out/(name+'.stderr')).read_bytes()),
             'minimal_environment_no_credentials':True}
    write(out/(name+'.execution.json'),receipt)
    if process.returncode or timeout: raise RuntimeError(name+' failed or exhausted resources; logs preserved in '+str(out))
    return receipt

def common_args(out,request_hash):
    return ['--request',str(out/'REQUEST.json'),'--request-sha256',request_hash,'--checkpoints',str(out/'journal')]

def checker_command(out,request_hash):
    engine=out/'runtime'/identities()['engine_directory']
    return [sys.executable,'-B',str(engine/'global_check.py'),*common_args(out,request_hash),'--source-pins',str(out/'CHECKER-PINS.json'),
            '--source-pins-sha256',sha((out/'CHECKER-PINS.json').read_bytes()),'--normal']

def inventory(out):
    return [{'path':str(p.relative_to(out)),'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
            for p in sorted(out.rglob('*')) if p.is_file() and p.name!='ARTIFACTS.json']

def report(out,result):
    state=result['execution_mode'];status=result['status'];lines=['# Practical nine-parameter solver', '', '**'+state+' — '+status+'**','',result['explanation'],'',
      'This computation is conditional on the supplied arithmetic constraints and the fixed model. Source existence, statistical confidence, and observed biological parameter accuracy are not certified.','']
    if result.get('widths'):
        lines+=['| Parameter | Normalized whole-union width | Target met |','|---|---:|---|']
        for key in PHYSICAL:
            row=result['widths'][key];value=row['normalized_ratio'];approx='empty' if value is None else format(float(Fraction(value)),'.10g')
            lines += ['| '+key+' | '+approx+' | '+str(row['met'])+' |']
        lines+=['','All complete retained cover cells are in RESULT.json. Exact rational widths are preserved; decimal display is only for reading.']
    lines+=['','Assumptions: labelled phased A1,A2,B1,B2,C1,C2 copies; complete two-site loci sharing one genealogy; fixed backward B-to-C pulse; original shared rates and pulse/rate ties; stationary homogeneous clock-JC. Shifted character means enter once; the inherited initializer converts to raw parity once.','',
      'Native/reference stage: '+result.get('diagnostic_description','not called')+'. This stage cannot alter or promote the checked cover.','',
      'Evidence files: RESULT.json, REQUEST.json when admitted, complete producer/checker logs and executions, CHECKER-PINS.json, SOURCE-IDENTITIES.json, journal/ and ARTIFACTS.json. Hashes detect byte changes; they are not signatures or a confidence proof.']
    text='\n'.join(lines)+'\n';(out/'REPORT.md').write_text(text)
    banner='Fresh run' if state=='FRESH_RUN' else 'Saved results — no solver executed' if state=='SAVED_RESULTS' else state.replace('_',' ').title()
    page='<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width"><title>Practical solver report</title><style>body{font:17px/1.55 system-ui;margin:2rem auto;max-width:1000px;padding:0 1rem}header{padding:1rem;background:#e6f0fc;border-left:5px solid #2868ad}pre{white-space:pre-wrap;overflow-wrap:anywhere}a{color:#175e9d}</style><header><strong>'+html.escape(banner)+'</strong><br>'+html.escape(status)+'</header><pre>'+html.escape(text)+'</pre><p><a href="RESULT.json">Machine-readable complete evidence</a> · <a href="REPORT.md">Markdown report</a> · <a href="ARTIFACTS.json">Artifact hashes</a></p></html>\n'
    (out/'REPORT.html').write_text(page)

def explanation(checked,label=None):
    if checked['status']=='CONDITIONAL_UNION_WIDTH_CERTIFIED':
        return 'Every normalized original-coordinate whole-union width is at most 1/20 after independent whole-journal replay. This is informative numerical localization of supplied near-exact arithmetic means, not observed-data accuracy.'
    if checked['status']=='EMPTY_COMPATIBLE_SET':
        return 'The independent complete-journal checker excludes the supplied feature bands under the fixed model and original full domain. No compatible source remains in this conditional outer cover. This diagnoses incompatible model constraints; it does not validate or invalidate the biological experiment.'
    if checked['status']=='EVIDENCE_INVALID':
        return 'The independent checker rejected the request evidence. No numerical certificate can be issued; inspect the preserved checker logs and input identity.'
    if label=='finite-data':
        return 'UNKNOWN: the existing 1,024-locus synthetic bands retain a broad complete outer cover. Two authenticated compatible source points differ by normalized rA = 3/55 > 1/20; unchanged bands cannot certify the all-nine target. Better inversion alone cannot remove this ambiguity. New admissible data, justified altered statistics or a different sampling design must be specified and validated. The finite-RNG law and scientific confidence are unverified.'
    return 'UNKNOWN: the complete checked outer cover remains wider than the requested target or replay was incomplete. The cover may contain non-solutions; retained cells are not verified feasible source assignments. Narrower scientifically justified observation bands or more computation may help, but sufficiency is not established for this input. Stop reason: '+str(checked.get('details',{}))[:500]

def run(args):
    source=APP/'examples'/f'{args.example}.json' if args.example else args.request
    raw,request=read(source)
    if args.example and sha(raw)!=EXAMPLE_SHAS[args.example]:raise SourceError('Example source identity mismatch')
    reason=admit(request);out=create_output(args.output)
    result={'schema':'practical_solver_release_result_v1','execution_mode':'FRESH_RUN','started_utc':datetime.now(timezone.utc).isoformat(),
       'request_sha256':sha(raw),'example':args.example,'source_feasibility_certified':False,'statistical_coverage_verified':False,
       'parameter_accuracy_released':False,'whole_application_lean_verified':False,'program_sha256':sha(Path(__file__).read_bytes())}
    try:
        if reason:
            result.update(status='MODEL_NOT_ADMITTED',explanation=reason,solver_called=False,required_model=MODEL)
        else:
            with (out/'REQUEST.json').open('xb') as f:f.write(raw)
            runtime,engine=stage(out);before=authenticate(out)
            executions=[execute(out,'producer',[sys.executable,'-B',str(engine/'global_engine.py'),*common_args(out,sha(raw))]),
                        execute(out,'checker',checker_command(out,sha(raw)))]
            _,checked=read(out/'checker.stdout',16*2**20)
            result.update(status=checked['status'],solver_called=True,original_complete_checker=checked,
                          retained_complete_outer_cover=checked.get('physical_cover',[]),widths=checked.get('widths'),executions=executions,
                          source_bytes_unchanged=before==authenticate(out),explanation=explanation(checked,args.example))
            if args.example=='finite-data':
                obstruction=INHERITED/'finite-data/PAIR-WIDTH-OBSTRUCTION.json';body=obstruction.read_bytes()
                if obstruction.is_symlink() or sha(body)!=OBSTRUCTION_SHA:raise SourceError('Finite-data obstruction identity mismatch')
                (out/'FINITE-DATA-OBSTRUCTION.json').write_bytes(body)
                result['saved_finite_data_obstruction']={'execution_mode':'SAVED_AUTHENTICATED_EVIDENCE','sha256':sha(body),
                    'source':str(obstruction.relative_to(ROOT)),'note':'Historical exact pair-containment evidence; solver above freshly rerun.'}
            diagnostic_args=[sys.executable,'-B',str(APP/'diagnostic.py'),'--request',str(out/'REQUEST.json'),'--checker',str(out/'checker.stdout'),'--output',str(out/'diagnostic')]
            if args.native_binary: diagnostic_args+=['--native-binary',str(args.native_binary.absolute())]
            try:
                receipt=execute(out,'diagnostic',diagnostic_args);_,diag=read(out/'diagnostic/RESULT.json',16*2**20)
                result.update(native_reference_post_checker=diag,diagnostic_execution=receipt,diagnostic_description=diag['description'])
            except Exception as error:
                result.update(native_reference_post_checker={'status':'DIAGNOSTIC_FAILED','reason':str(error)},diagnostic_description='optional diagnostic failed; complete checked cover preserved')
    except Exception as error:
        result.update(status='RESOURCE_OR_EXECUTION_FAILURE',explanation=str(error),solver_called=True)
    result['ended_utc']=datetime.now(timezone.utc).isoformat();write(out/'RESULT.json',result);report(out,result);write(out/'ARTIFACTS.json',inventory(out))
    print(json.dumps({'status':result['status'],'execution_mode':result['execution_mode'],'output':str(out),'report':str(out/'REPORT.html')},sort_keys=True))
    return 1 if result['status']=='RESOURCE_OR_EXECUTION_FAILURE' else 0

def show(args):
    mapping={'informative':'original-multistage','finite-data':'finite-data','unsupported':'cli-model-mismatch'}
    source=INHERITED/mapping[args.example]/'RESULT.json';raw,saved=read(source,16*2**20,exact=False)
    if sha(raw)!=SAVED_SHAS[args.example]:raise SourceError('Saved historical result identity mismatch')
    out=create_output(args.output)
    checked=saved.get('checker',saved.get('original_complete_checker',{}))
    result={'schema':'practical_solver_release_result_v1','execution_mode':'SAVED_RESULTS','status':checked.get('status',saved.get('status')),
      'explanation':'Saved 8 October 2026 evidence displayed. No solver, checker, native binary or service was executed by this command.',
      'saved_source':str(source.relative_to(ROOT)),'saved_source_sha256':sha(raw),'saved_result':saved,'widths':checked.get('widths'),
      'source_feasibility_certified':False,'statistical_coverage_verified':False,'parameter_accuracy_released':False,'solver_called':False}
    write(out/'RESULT.json',result);report(out,result);write(out/'ARTIFACTS.json',inventory(out))
    print(json.dumps({'execution_mode':'SAVED_RESULTS','status':result['status'],'output':str(out)},sort_keys=True));return 0

def check(args):
    source=args.run.absolute();raw,request=read(source/'REQUEST.json');reason=admit(request)
    if reason:raise InputError(reason)
    _,previous=read(source/'RESULT.json',16*2**20,exact=False)
    if sha(raw)!=previous.get('request_sha256'):raise InputError('Request hash differs from saved run identity')
    authenticate(source);frames=list((source/'journal').glob('state-*.json'))
    if len(frames)>MAX_FRAMES or sum(p.stat().st_size for p in frames)>MAX_JOURNAL_BYTES:raise InputError('Journal resource limit exceeded')
    for p in frames:
        if p.is_symlink() or p.stat().st_size>8*2**20:raise InputError('Journal must use bounded nonsymlink frames')
    out=create_output(args.output);receipt=execute(out,'checker',checker_command(source,sha(raw)));_,checked=read(out/'checker.stdout',16*2**20)
    result={'schema':'practical_solver_release_recheck_v1','execution_mode':'FRESH_INDEPENDENT_RECHECK','status':checked['status'],
      'explanation':explanation(checked),'source_run':str(source),'request_sha256':sha(raw),'original_complete_checker':checked,
      'retained_complete_outer_cover':checked.get('physical_cover',[]),'widths':checked.get('widths'),'execution':receipt,
      'source_feasibility_certified':False,'statistical_coverage_verified':False,'parameter_accuracy_released':False}
    write(out/'RESULT.json',result);report(out,result);write(out/'ARTIFACTS.json',inventory(out))
    print(json.dumps({'execution_mode':result['execution_mode'],'status':result['status'],'output':str(out)},sort_keys=True));return 0

def molecular(args):
    out=create_output(args.output)
    adapter=APP.parent/'practical-solver-biology/offline.py'
    receipt=execute(out,'offline-molecular',[sys.executable,'-B',str(adapter),'--output',str(out/'molecular')])
    _,result=read(out/'molecular/RESULT.json',16*2**20,exact=False)
    result.update(execution_mode='FRESH_OFFLINE_FIXTURE_COMPUTATION',execution=receipt,
                  adapter_sha256=sha(adapter.read_bytes()),ancestry_observation_admitted=False)
    write(out/'RESULT.json',result)
    for name in ('REPORT.html','REPORT.md','REQUEST.json'):
        with (out/name).open('xb') as target:target.write((out/'molecular'/name).read_bytes())
    write(out/'ARTIFACTS.json',inventory(out))
    print(json.dumps({'execution_mode':result['execution_mode'],'status':result['status'],'evidence':result['evidence'],
                      'live_api_calls':0,'output':str(out)},sort_keys=True));return 0

def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='command',required=True)
    fresh=sub.add_parser('run',help='Fresh producer + independent complete-journal checker + pair diagnostic')
    inp=fresh.add_mutually_exclusive_group(required=True);inp.add_argument('--example',choices=['informative','finite-data','unsupported']);inp.add_argument('--request',type=Path)
    fresh.add_argument('--output',type=Path);fresh.add_argument('--native-binary',type=Path);fresh.set_defaults(func=run)
    saved=sub.add_parser('show',help='Display explicitly saved evidence without running solver');saved.add_argument('--example',choices=['informative','finite-data','unsupported'],required=True);saved.add_argument('--output',type=Path);saved.set_defaults(func=show)
    recheck=sub.add_parser('check',help='Independently replay a prior complete journal');recheck.add_argument('--run',type=Path,required=True);recheck.add_argument('--output',type=Path);recheck.set_defaults(func=check)
    mol=sub.add_parser('molecular',help='Fresh optional matched REF/A/B/AB synthetic fixture; zero live calls')
    mol.add_argument('--output',type=Path);mol.set_defaults(func=molecular)
    args=parser.parse_args()
    try:return args.func(args)
    except (InputError,SourceError,OSError,ValueError,RuntimeError) as error:print('ERROR: '+str(error),file=sys.stderr);return 2

if __name__=='__main__':raise SystemExit(main())
