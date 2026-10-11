#!/usr/bin/env python3
"""Reproduce pinned builds, exact reference/corpus controls and bounded benchmarks.

Requires an existing approved Rust1.90 toolchain. Does not provision software.
All subprocesses are sequential; no Lean compiler or deployed application runs.
"""
from pathlib import Path
import argparse, csv, datetime, hashlib, json, os, resource, shutil, statistics
import subprocess, sys, time
from fractions import Fraction

ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[1]
BASE=REPO/'research/2026-10-08-cloud-rust-interval-root-0000z'
EVIDENCE=ROOT/'evidence'

def sha(data): return hashlib.sha256(data).hexdigest()
def dump(name,value): (EVIDENCE/name).write_text(json.dumps(value,indent=2)+'\n')
def source_pins():
    return {str(p.relative_to(REPO)):sha(p.read_bytes()) for p in
            [*sorted((ROOT/'crate').rglob('*.rs')),ROOT/'crate/Cargo.toml',ROOT/'crate/Cargo.lock',
             ROOT/'run_checks.py',BASE/'src/lib.rs',BASE/'src/main.rs',BASE/'src/parse.rs',
             BASE/'Cargo.lock',BASE/'Cargo.toml',BASE/'reference/certified_forward.py',
             BASE/'reference/signed_receiver.py',BASE/'differential_check.py',
             BASE/'reports/cloud-differential/run-once/corpus-and-expected.json',
             BASE/'reports/cloud-differential/run-once/probe.stdin.tsv',
             BASE/'reports/cloud-differential/run-once/probe.stdout.tsv']}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--toolchain',type=Path,required=True)
    parser.add_argument('--scratch',type=Path,required=True)
    parser.add_argument('--mutations',action='store_true')
    args=parser.parse_args();args.scratch.mkdir(parents=True,exist_ok=True)
    EVIDENCE.mkdir(exist_ok=True)
    env=os.environ.copy();env.update(PATH=str(args.toolchain/'bin')+os.pathsep+env['PATH'],
        CARGO_HOME=str(args.scratch/'cargo-cache'),CARGO_TARGET_DIR=str(args.scratch/'target'))
    receipts=[];before=source_pins();dump('source-pins-before.json',before)

    def run(label,command,cwd=ROOT/'crate',stdin=None,expected_exit=0,target=None):
        runenv=env.copy()
        if target:runenv['CARGO_TARGET_DIR']=str(target)
        usage0=resource.getrusage(resource.RUSAGE_CHILDREN);t0=time.perf_counter()
        p=subprocess.run([str(x) for x in command],cwd=cwd,env=runenv,input=stdin,
                         stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=180)
        wall=time.perf_counter()-t0;usage1=resource.getrusage(resource.RUSAGE_CHILDREN)
        (EVIDENCE/(label+'.stdout')).write_bytes(p.stdout)
        (EVIDENCE/(label+'.stderr')).write_bytes(p.stderr)
        receipts.append({'label':label,'command':[str(x) for x in command],
            'cwd':str(cwd),'exit':p.returncode,'wall_seconds':wall,
            'child_cpu_seconds':usage1.ru_utime+usage1.ru_stime-usage0.ru_utime-usage0.ru_stime,
            'children_cumulative_maxrss_kib':usage1.ru_maxrss,
            'stdout_sha256':sha(p.stdout),'stderr_sha256':sha(p.stderr),
            'stdin_sha256':None if stdin is None else sha(stdin)})
        dump('execution.json',receipts)
        assert p.returncode==expected_exit,(label,p.returncode,p.stderr[-2000:])
        print(label,'exit',p.returncode,round(wall,4),flush=True)
        return p

    run('rustc-version',[args.toolchain/'bin/rustc','--version','--verbose'])
    run('cargo-version',[args.toolchain/'bin/cargo','--version'])
    run('locked-fetch',[args.toolchain/'bin/cargo','fetch','--locked'])
    run('release-tests',[args.toolchain/'bin/cargo','test','--release','--locked','--offline'])
    run('release-build',[args.toolchain/'bin/cargo','build','--release','--locked','--offline','--bins'])
    run('allocation-build',[args.toolchain/'bin/cargo','build','--release','--locked','--offline',
                           '--features','allocation-counts','--bin','cache-bench'],target=args.scratch/'allocation-target')
    run('baseline-build',[args.toolchain/'bin/cargo','build','--release','--locked','--offline','--bin','interval-probe'],
        cwd=BASE,target=args.scratch/'baseline-target')

    # Load unchanged legacy harness/reference bytes. Recompute each saved case,
    # rather than changing its corpus generator or expecting a new Unicode set.
    harness_data=(BASE/'differential_check.py').read_bytes()
    assert sha(harness_data)=='ad79b676870221b6ca0ca101655ae42ffa40fc56f7261fd1009385028ee602e6'
    import types
    harness=types.ModuleType('frozen_differential');harness.__file__=str(BASE/'differential_check.py')
    exec(compile(harness_data,harness.__file__,'exec'),harness.__dict__)
    for name,want in harness.PINNED.items(): assert sha((BASE/name).read_bytes())==want,name
    reference_root=args.scratch/'reference-root';staged=reference_root/harness.PROVIDER
    staged.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(BASE/'reference/certified_forward.py',staged)
    f=harness.load_exact('frozen_forward',(BASE/'reference/certified_forward.py').read_bytes(),BASE/'reference/certified_forward.py')
    r=harness.load_exact('frozen_receiver',(BASE/'reference/signed_receiver.py').read_bytes(),BASE/'reference/signed_receiver.py')
    frozen=BASE/'reports/cloud-differential/run-once'
    cases=json.loads((frozen/'corpus-and-expected.json').read_text())
    started=time.perf_counter()
    recomputed=[harness.expected(row['case'],f,r,reference_root) for row in cases]
    differences=[row['case']['id'] for row,new in zip(cases,recomputed) if row['expected']['wire']!=new['wire']]
    dump('python-reference.json',{'cases':len(cases),'wire_matches':len(cases)-len(differences),
        'differences':differences,'elapsed_seconds':time.perf_counter()-started,
        'python':sys.version,'reference_cache_unchanged':True})
    assert not differences,differences
    inputs=(frozen/'probe.stdin.tsv').read_bytes();wanted=(frozen/'probe.stdout.tsv').read_bytes()
    assert inputs==(''.join(row['case']['input_line']+'\n' for row in cases)).encode()
    assert wanted==(''.join(row['expected']['wire']+'\n' for row in cases)).encode()
    probe=args.scratch/'target/release/interval-probe'
    summaries=[]
    for label,command in [('baseline-corpus',[args.scratch/'baseline-target/release/interval-probe']),
            ('revision-uncached-corpus',[probe]),('revision-cache0-corpus',[probe,'--cache-entries','0']),
            ('revision-cache64-corpus',[probe,'--cache-entries','64']),
            ('revision-cache1-corpus',[probe,'--cache-entries','1'])]:
        result=run(label,command,stdin=inputs)
        actual=result.stdout.splitlines();expected=wanted.splitlines()
        mismatches=[i+1 for i,(a,b) in enumerate(zip(actual,expected)) if a!=b]
        summaries.append({'label':label,'cases':len(cases),'actual_rows':len(actual),
            'exact_matches':len(cases)-len(mismatches),'differences':mismatches,
            'stdout_equal':result.stdout==wanted,'cache_stats':result.stderr.decode().strip()})
        dump('corpus.json',summaries)
        assert result.stdout==wanted,(label,mismatches[:10],len(actual))

    # Alternating order limits systematic cold/warm scheduling bias. Cache is
    # recreated each repetition; first population/miss cost remains timed.
    bench=args.scratch/'target/release/cache-bench'
    allocation_bench=args.scratch/'allocation-target/release/cache-bench';benches=[]
    for index,(workload,capacity) in enumerate([('repeated-1',64),('repeated-8',64),
            ('unique',64),('repeated-8',4),('shortcut',64)]):
        records={};outputs={}
        for round_number in range(3):
            for cap in ([0,capacity] if round_number%2==0 else [capacity,0]):
                label=f'bench-{index}-{workload}-cap{cap}-round{round_number}'
                result=run(label,[bench,workload,str(cap),'3','128'])
                records.setdefault(cap,[]).extend(list(csv.DictReader(result.stdout.decode().splitlines(),delimiter='\t')))
                outputs.setdefault(cap,set()).add(result.stderr)
        assert len(outputs[0])==len(outputs[capacity])==1
        assert outputs[0]==outputs[capacity]
        data={'workload':workload,'calls_per_repetition':128,'bits':128,'repetitions':9,
              'cache_capacity':capacity,'output_sha256':sha(next(iter(outputs[0]))),
              'input_rule':{'repeated-1':'128 copies of 1/3','repeated-8':'(i % 8 + 1)/9',
                            'unique':'(i+1)/129','shortcut':'128 + i % 8'}[workload],
              'exact_cached_uncached_outputs_equal':True,'modes':{}}
        for cap,rows in records.items():
            data['modes'][str(cap)]={
                'median_'+key:statistics.median(int(row[key]) for row in rows)
                for key in ['wall_ns','cpu_ns','alloc_events','requested_bytes','peak_extra_live','hits',
                            'misses','bypasses','evaluations','taylor_terms','squarings','evictions']}
        allocation={}
        for cap in [0,capacity]:
            result=run(f'alloc-{index}-{workload}-cap{cap}',[allocation_bench,workload,str(cap),'1','128'])
            assert {result.stderr}==outputs[cap]
            row=list(csv.DictReader(result.stdout.decode().splitlines(),delimiter='\t'))[0]
            allocation[str(cap)]={key:int(row[key]) for key in ['alloc_events','requested_bytes','peak_extra_live']}
        data['separate_allocation_measurement']=allocation
        data['timing_allocator']='default System; allocation-counts feature disabled'
        data['uncached_over_cached_median_wall']=data['modes']['0']['median_wall_ns']/data['modes'][str(capacity)]['median_wall_ns']
        literal=''.join(f'128\t{dict([("repeated-1",Fraction(1,3)),("repeated-8",Fraction(i%8+1,9)),("unique",Fraction(i+1,129)),("shortcut",Fraction(128+i%8))])[workload]}\n' for i in range(128)).encode()
        (EVIDENCE/f'bench-input-{index}.tsv').write_bytes(literal)
        data['input_sha256']=sha(literal)
        benches.append(data);dump('benchmarks.json',benches)

    if args.mutations:
        original=(ROOT/'crate/src/lib.rs').read_text();mutations=[]
        for name,old,new in [
            ('charge-erased','self.0.exp_calls.set(calls+2);','self.0.exp_calls.set(calls);'),
            ('precision-key-erased','x: x.clone(), bits, policy: EXP_POLICY','x: x.clone(), bits: 8, policy: EXP_POLICY'),
            ('argument-key-erased','x: x.clone(), bits, policy: EXP_POLICY','x: integer(0), bits, policy: EXP_POLICY')]:
            assert original.count(old)==1
            directory=args.scratch/'mutations'/name
            shutil.copytree(ROOT/'crate',directory,dirs_exist_ok=True)
            (directory/'src/lib.rs').write_text(original.replace(old,new))
            result=run('mutation-'+name,[args.toolchain/'bin/cargo','test','--release','--locked','--offline','--test','cache'],
                cwd=directory,target=args.scratch/'mutation-target',expected_exit=101)
            assert b'test result: FAILED' in result.stdout
            mutations.append({'name':name,'mutated_source_sha256':sha((directory/'src/lib.rs').read_bytes()),
                              'exit':result.returncode,'test_failure_observed':True})
        dump('mutations.json',mutations)

    after=source_pins();dump('source-pins-after.json',after);assert before==after
    dump('build-identities.json',{str(p):{'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
        for p in [probe,bench,allocation_bench,args.scratch/'baseline-target/release/interval-probe',
                  args.toolchain/'bin/rustc',args.toolchain/'bin/rustdoc',args.toolchain/'bin/cargo']})
    dump('RESULT.json',{'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source_identities_unchanged':True,'corpus_modes':5,'cases_per_mode':3048,
        'fresh_python_reference_wire_matches':3048,'inherited_unit_controls':10,
        'new_cache_controls':8,'benchmark_workloads':5,'benchmark_repetitions_per_mode':9,
        'mutations_rejected':3 if args.mutations else None,
        'limitations':['finite-tested arithmetic refinement, no universal proof',
            'synthetic kernel benchmarks, no deployed producer acceleration measurement',
            'process RSS receipt is cumulative RUSAGE_CHILDREN high-water, not per-kernel memory',
            'timing uses default allocator; separate allocation counts/bytes/live peak use Linux System allocator delegation',
            'Lean public payload verification separate; no fresh Lean compilation',
            'source/history/parser/master obligations remain open']})

if __name__=='__main__':main()
