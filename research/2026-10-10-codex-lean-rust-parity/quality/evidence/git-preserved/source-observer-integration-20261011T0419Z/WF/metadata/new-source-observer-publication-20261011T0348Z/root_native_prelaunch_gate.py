"""Fixed private run preflight; root scheduler still invokes the guarded run separately."""
import pathlib,hashlib,json,os,subprocess,datetime,sys,importlib.util
W=pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
G=W/'metadata/source-only-observer-execution-guard-20261011T0338Z'
D=pathlib.Path(__file__).resolve().parent
def pin(p):
    b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,sha):
    r=pin(p);assert r['sha256']==sha;return r
guard=check(G/'guard_erased_selected_observer_v1.py','e7416c8012edf64a4f84cf24c98bc79d22d070cf8f71008f9a080462edf3e723')
cp=check(G/'EXECUTION-CONFIG-V1.json','a04d75654f8e5126eb99ac082c79643e60c12621614e2e15e6a1448c2947a227')
cfg=json.loads(pathlib.Path(cp['path']).read_bytes())
hp=check(W/'metadata/erased-observer-harness-independent-qc-20261011T034947.152719Z-lean-reuse-successor/OBSERVER-HARNESS-MATHEMATICAL-ADEQUACY-QC.json','c6002f8ab1972fa0c53a66f870e11ca402252b13058398a33911b0c8add5632d')
qp=check(pathlib.Path(sys.argv[1]),sys.argv[2])
assert json.loads(pathlib.Path(hp['path']).read_bytes())['status'].startswith('PASS')
assert json.loads(pathlib.Path(qp['path']).read_bytes())['status'].startswith('PASS')
assert len(cfg['input_pins'])==64 and all(pin(pathlib.Path(r['path']))==r for r in cfg['input_pins'])
env={**os.environ,'GIT_OBJECT_DIRECTORY':'/tmp/rc-cloud-git-objects-20261010T223739.438030Z','GIT_ALTERNATE_OBJECT_DIRECTORIES':'/workspace/Research-Commons/.git/objects','GIT_INDEX_FILE':'/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT','GIT_OPTIONAL_LOCKS':'0'}
def git(*args):return subprocess.check_output(['git',*args],cwd='/workspace/Research-Commons',env=env,text=True).strip()
head=git('rev-parse','HEAD');tree=git('rev-parse','HEAD^{tree}')
assert head=='4862b9618ca422da4ad5381b5dec0a3fcac56e76' and tree=='145eefb4baaec4eafca16622ed9fdfb538313922'
spec=importlib.util.spec_from_file_location('fixed_private_guard_accounting',pathlib.Path(guard['path']))
q=importlib.util.module_from_spec(spec);spec.loader.exec_module(q)
roots=cfg['allocation_roots'];assert len(roots)==26
measured=q.measurements(roots);assert not q.limit_reason(measured)
assert measured['global_distinct_inode_allocated_bytes']+50331648<2013265920
assert not q.active_markers(roots) and not pathlib.Path(cfg['output_directory']).exists()
record={'status':'PASS_ROOT_FIXED_PRIVATE_EXECUTION_PREFLIGHT','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'guard':guard,'config':cp,'independent_harness_qc':hp,'independent_guard_qc':qp,'all64_input_pins_exact':True,'head':head,'tree':tree,'measurements':measured,'fixed_execution_reserve_bytes':50331648,'root_is_sole_native_scheduler':True,'scope':'Preflight only; actual root invocation and compiler/test outcome follow separately. Root will keep Git mutations idle for this slot. No user permission request, cache admission, public executable promotion, Lean/native refinement or master closure.'}
raw=(json.dumps(record,indent=2)+'\n').encode();assert len(raw)<16384
with (D/'ROOT-NATIVE-PRELAUNCH-GATE.json').open('xb') as f:f.write(raw)
print(json.dumps(record))
