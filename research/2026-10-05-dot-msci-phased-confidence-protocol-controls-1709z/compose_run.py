"""Fresh bounded extraction and inverse execution; never imports saved PASS caches."""
import hashlib,json,os,sys
from fractions import Fraction as F
from pathlib import Path
BASE=Path(__file__).resolve().parent
FILES=('integration_core.py','prepare_input.py','compose_run.py','prepare_fixtures.py')
def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write_new(path,value):
    with Path(path).open('x') as out:json.dump(value,out,sort_keys=True,indent=2);out.write('\n')
def authenticate(manifest,expected):
    if digest(manifest)!=expected:raise ValueError('externally trusted source/registry manifest identity')
    # Expected manifest is the externally reviewed release identity; inspect source
    # bytes before importing any execution-bearing local dependency.
    d=json.loads(Path(manifest).read_text())
    if not isinstance(d,dict) or set(d)!={'sources','admission_registry_sha256','provider_manifest_sha256'} or not isinstance(d['sources'],dict) or set(d['sources'])!=set(FILES):raise ValueError('runtime pin allowlist')
    for name,pin in d['sources'].items():
        q=BASE/name
        if q.is_symlink() or digest(q)!=pin:raise ValueError('source changed')
    import integration_core as c
    if d['admission_registry_sha256']!=c.TRUSTED_REGISTRY_SHA:raise c.NotAdmitted('registry is not anchored in reviewed source')
    if (BASE/'ADMISSION-REGISTRY.json').is_symlink() or digest(BASE/'ADMISSION-REGISTRY.json')!=d['admission_registry_sha256']:raise c.NotAdmitted('trusted admission registry changed')
    if d['provider_manifest_sha256']!=c.PROVIDER_MANIFEST_SHA:raise c.EvidenceInvalid('inverse provider identity')
    c.load_provider()
    return d

def copy_input(source,target,expected):
    import integration_core as c
    p=Path(source)
    if p.is_symlink() or p.stat().st_size>c.MAX_BYTES:raise c.InputResource('input file cap/link')
    raw=p.read_bytes()
    if len(raw)>c.MAX_BYTES or c.sha(raw)!=expected:raise c.EvidenceInvalid('input copy identity')
    with Path(target).open('xb') as out:out.write(raw)

def report(preparation,confidence,inverse,request,provider):
    """Called only with the current fresh checker's hash-authenticated output."""
    mode=inverse.get('mode')
    if mode not in ('normal_validated','recovered_same_process_validated_prefix'):raise ValueError('unverified numerical output mode')
    if inverse.get('request_sha256')!=preparation['inverse_request_sha256'] or inverse.get('model')!=provider.MODEL:raise ValueError('inverse identity')
    if inverse.get('ranked_histories') is not None or inverse.get('recommended_history') is not None or inverse.get('parameter_accuracy_released') or inverse.get('statistical_coverage_verified'):raise ValueError('unexpected provider release')
    if mode=='normal_validated' and inverse['details'].get('complete_numeric_replay') is not True:raise ValueError('incomplete normal replay')
    if mode=='recovered_same_process_validated_prefix' and not inverse['details'].get('resource_limited'):raise ValueError('invalid prefix recovery')
    boxes=inverse['physical_cover']
    if not isinstance(boxes,list) or not isinstance(inverse['augmented_states'],list) or len(boxes)!=len(inverse['augmented_states']):raise ValueError('cover schema')
    frontier={};seen=set()
    for cell,aug in zip(boxes,inverse['augmented_states']):
        if cell['id'] in seen or cell['id']!=aug['id'] or cell['box']!=aug['state']['physical']:raise ValueError('complete exported physical cover mismatch')
        seen.add(cell['id'])
        if set(cell['box'])!=set(provider.ops.PHYSICAL):raise ValueError('physical dimension mismatch')
        parsed={}
        for name,bounds in cell['box'].items():
            if not isinstance(bounds,list) or len(bounds)!=2 or any(not isinstance(x,str) or len(x)>4096 for x in bounds):raise ValueError('output interval encoding')
            lo,hi=(provider.m.size_guard(F(x)) for x in bounds)
            if lo>hi or lo<request['physical'][name].lo or hi>request['physical'][name].hi:raise ValueError('export outside original domain')
            parsed[name]=provider.m.I(lo,hi)
        frontier[cell['id']]={'state':{'physical':parsed}}
    met,widths=provider.goal(request,frontier)
    if widths!=inverse['widths'] or met!=inverse['diagnostic_union_width_target_observed'] or (met and mode=='normal_validated')!=inverse['whole_union_width_target_met']:raise ValueError('whole-union width mismatch')
    if preparation['admission_classification'] not in ('protocol_fixture','scientifically_admitted'):raise ValueError('unknown admission classification')
    scientific=preparation['admission_classification']=='scientifically_admitted'
    status='CONDITIONAL_INCOMPATIBILITY' if not boxes else ('CONDITIONAL_CONFIDENCE_WIDTH_MET' if met and mode=='normal_validated' else 'UNKNOWN_CONDITIONAL_OUTER_COVER')
    if not scientific:status='PROTOCOL_ONLY_'+status
    return {'schema':'phased-locus-conditional-cover-v1','status':status,'admission_classification':preparation['admission_classification'],'scientific_premises':preparation['scientific_premises'],'dataset_sha256':preparation['dataset_sha256'],'admission_sha256':preparation['admission_sha256'],'analysis_request_sha256':preparation['analysis_request_sha256'],'trusted_registry_sha256':preparation['trusted_registry_sha256'],'delta':confidence['delta'],'confidence_construction':confidence['mode'],'confidence_error_upper_bound':confidence['error_upper_bound'],'statistical_bound_conditional_on_A1_to_A6':True,'data_confidence_certificate_eligible':scientific,'data_confidence_certificate_issued':False,'requires_successful_terminal_inventory':True,'false_issued_certificate_error_bound':confidence['delta'] if scientific else None,'coverage_conditional_on_success_claimed':False,'posterior_claimed':False,'numerical_mode':mode,'complete_numeric_replay':inverse['details'].get('complete_numeric_replay',False),'original_domain_preserved':True,'physical_cover':boxes,'nonempty_cover':bool(boxes),'widths':widths,'whole_union_width_target_met':met and mode=='normal_validated','diagnostic_union_width_target_observed':met,'source_feasibility_certified':False,'ranked_histories':None,'recommended_history':None,'inverse_request_sha256':preparation['inverse_request_sha256'],'extraction_sha256':preparation['extraction_sha256'],'confidence_sha256':preparation['confidence_sha256']}

def run(request_path,request_sha,dataset_path,admission_path,attempt,manifest,manifest_sha):
    pins=authenticate(manifest,manifest_sha)
    import integration_core as c
    provider=c.load_provider();import bounded_runner as runner
    attempt=Path(attempt).absolute();attempt.mkdir(exist_ok=False);prep_stage=None;inverse_terminal=None;inverse_started=False;final=None;error=None
    try:
        req,_=c.request(request_path,request_sha)
        for source,name,identity in [(request_path,'ANALYSIS-REQUEST.json',request_sha),(dataset_path,'DATASET.json',req['dataset_sha256']),(admission_path,'ADMISSION.json',req['admission_sha256'])]:copy_input(source,attempt/name,identity)
        write_new(attempt/'BEFORE.json',{'manifest_sha256':manifest_sha,'pins':pins,'request_sha256':request_sha,'dataset_sha256':req['dataset_sha256'],'admission_sha256':req['admission_sha256']})
        command=[sys.executable,str(BASE/'prepare_input.py'),'--request',str(attempt/'ANALYSIS-REQUEST.json'),'--request-sha256',request_sha,'--dataset',str(attempt/'DATASET.json'),'--admission',str(attempt/'ADMISSION.json'),'--registry',str(BASE/'ADMISSION-REGISTRY.json'),'--registry-sha256',pins['admission_registry_sha256'],'--output',str(attempt/'prepared')]
        prep_stage=runner.stage(command,attempt,'prepare',runner.load_watchdog(),wall=30)
        if prep_stage['status']!='EXECUTION_EXIT_ZERO':raise ValueError('no complete preparation execution')
        prep_path=attempt/'prepared/PREPARATION.json';preparation=c.read(prep_path,digest(prep_path))
        if preparation['status'] not in ('COMPLETE_PROTOCOL_PREPARATION','COMPLETE_ADMITTED_PREPARATION'):
            final={'schema':'phased-locus-conditional-cover-v1','status':preparation['status'],'input_reason':preparation.get('reason'),'complete_extraction':False,'data_confidence_certificate_issued':False,'physical_cover':None,'whole_union_width_target_met':False,'ranked_histories':None,'recommended_history':None}
        else:
            if preparation['analysis_request_sha256']!=request_sha or preparation['trusted_registry_sha256']!=pins['admission_registry_sha256'] or preparation['dataset_sha256']!=req['dataset_sha256'] or preparation['admission_sha256']!=req['admission_sha256'] or preparation['extractor_sha256']!=pins['sources']['integration_core.py']:raise ValueError('fresh preparation provenance')
            admitted=c.admission(attempt/'ADMISSION.json',BASE/'ADMISSION-REGISTRY.json',pins['admission_registry_sha256'],req)
            if preparation['admission_classification']!=admitted['classification'] or preparation['scientific_premises']!=admitted['premises'] or preparation['provider_manifest_sha256']!=c.PROVIDER_MANIFEST_SHA:raise ValueError('fresh admission/provider binding')
            confidence=c.read(attempt/'prepared/CONFIDENCE.json',preparation['confidence_sha256']);extraction=c.read(attempt/'prepared/EXTRACTION.json',preparation['extraction_sha256'])
            if extraction['m']!=req['expected_loci'] or extraction['selection_sha256']!=req['selection_sha256'] or confidence['m']!=req['expected_loci'] or F(confidence['delta'])!=F(req['delta']):raise ValueError('confidence/sample/design binding')
            rebuilt=c.inverse_request(req,confidence,request_sha,preparation['extraction_sha256'],preparation['confidence_sha256'])
            if c.sha(c.canonical(rebuilt))!=preparation['inverse_request_sha256']:raise ValueError('feature box/domain/request binding')
            inverse_path=attempt/'prepared/INVERSE-REQUEST.json';parsed=provider.read_request(inverse_path,preparation['inverse_request_sha256'])
            provider_pins=c.read(c.PROVIDER/'SOURCE-PINS.json',c.PROVIDER_MANIFEST_SHA)
            checker_pins=attempt/'CHECKER-PINS.json';write_new(checker_pins,{name:provider_pins[name] for name in (*provider.SOURCE_FILES,'global_check.py')})
            common=['--request',str(inverse_path),'--request-sha256',preparation['inverse_request_sha256'],'--checkpoints',str(attempt/'journal')]
            watchdog=runner.load_watchdog()
            inverse_started=True
            producer=runner.stage([sys.executable,str(c.PROVIDER/'global_engine.py'),*common],attempt,'producer',watchdog)
            if producer['status']!='EXECUTION_EXIT_ZERO':raise ValueError('no completed producer execution')
            authenticate(manifest,manifest_sha)
            checker=runner.stage([sys.executable,str(c.PROVIDER/'global_check.py'),*common,'--source-pins',str(checker_pins),'--source-pins-sha256',digest(checker_pins),'--normal'],attempt,'checker',watchdog)
            if checker['status']!='EXECUTION_EXIT_ZERO':raise ValueError('no completed checker execution')
            authenticate(manifest,manifest_sha)
            inverse=c.read(attempt/'checker.stdout',digest(attempt/'checker.stdout'))
            inverse_terminal={'producer':producer,'checker':checker,'inverse_request_sha256':preparation['inverse_request_sha256'],'provider_manifest_sha256':c.PROVIDER_MANIFEST_SHA,'checker_output_sha256':digest(attempt/'checker.stdout'),'no_saved_cache_accepted':True}
            write_new(attempt/'INVERSE-EXECUTION.json',inverse_terminal)
            final=report(preparation,confidence,inverse,parsed,provider)
            final['fresh_inverse_execution_sha256']=digest(attempt/'INVERSE-EXECUTION.json');final['checker_output_sha256']=digest(attempt/'checker.stdout')
        authenticate(manifest,manifest_sha)
        for name,identity in [('ANALYSIS-REQUEST.json',request_sha),('DATASET.json',req['dataset_sha256']),('ADMISSION.json',req['admission_sha256'])]:
            if digest(attempt/name)!=identity:raise ValueError('copied input changed')
    except (OSError,ValueError,TypeError,KeyError,IndexError,ArithmeticError,RecursionError) as exc:
        error={'type':type(exc).__name__,'reason':str(exc)};status='NOT_ADMITTED' if isinstance(exc,c.NotAdmitted) else ('INPUT_RESOURCE_LIMIT' if isinstance(exc,c.InputResource) else ('EVIDENCE_INVALID' if isinstance(exc,c.EvidenceInvalid) else 'NO_NEW_CERTIFICATE'));final={'schema':'phased-locus-conditional-cover-v1','status':status,'error':error,'data_confidence_certificate_issued':False,'physical_cover':None,'whole_union_width_target_met':False,'ranked_histories':None,'recommended_history':None}
    output_failure=None;inventory_failure=None;inventory={};size=None;output_sha=None
    try:
        write_new(attempt/'COMPOSED-RESULT.json',final);output_sha=digest(attempt/'COMPOSED-RESULT.json')
    except Exception as exc:output_failure={'type':type(exc).__name__,'reason':str(exc)}
    try:
        watchdog=runner.load_watchdog();size=watchdog.tree_bytes(attempt)
        for path in sorted(attempt.rglob('*')):
            if path.is_file() and not path.is_symlink():inventory[str(path.relative_to(attempt))]={'sha256':digest(path),'bytes':path.stat().st_size}
    except Exception as exc:inventory_failure={'type':type(exc).__name__,'reason':str(exc)}
    terminal={'schema':'fresh-phased-confidence-attempt-v1','source_manifest_sha256':manifest_sha,'request_sha256':request_sha,'preparation_stage':prep_stage,'fresh_inverse_executed':inverse_started,'fresh_inverse_verified':inverse_terminal is not None,'error':error,'output_failure':output_failure,'inventory_failure':inventory_failure,'bytes_before_terminal':size,'inventory':inventory,'composed_output_sha256':output_sha,'data_confidence_certificate_issued':bool(final and final.get('data_confidence_certificate_eligible',False) and error is None and not output_failure and not inventory_failure)}
    write_new(attempt/'TERMINAL.json',terminal);return terminal
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser()
    for name in ('request','request-sha256','dataset','admission','attempt','source-manifest','source-manifest-sha256'):p.add_argument('--'+name,required=True)
    a=p.parse_args();print(json.dumps(run(a.request,a.request_sha256,a.dataset,a.admission,a.attempt,a.source_manifest,a.source_manifest_sha256),sort_keys=True,indent=2))
