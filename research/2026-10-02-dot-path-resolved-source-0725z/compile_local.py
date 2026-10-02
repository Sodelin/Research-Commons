import re,sys,subprocess,os,pathlib,time,resource,json,hashlib,shutil
B=pathlib.Path('/workspace/shared/lean-formalization');L=pathlib.Path(__file__).parent.resolve();name=sys.argv[1];limit=int(sys.argv[2]) if len(sys.argv)>2 else 60;memory=int(sys.argv[3]) if len(sys.argv)>3 else 4096
p=L/f'{name}.lean';data=p.read_bytes();h=hashlib.sha256(data).hexdigest();frozen=L/'receipts'/h/('attempt-'+str(time.time_ns()));frozen.mkdir(parents=True);(frozen/p.name).write_bytes(data)
env=os.environ.copy();env['PATH']=str(B/'tooling/lean-4.33.1-linux/bin')+':'+env['PATH'];env['LEAN_PATH']=':'.join(map(str,[L/'objects',B/'build/objects',B/'build/mathlib/.lake/build/lib/lean']+list((B/'build/mathlib/.lake/packages').glob('*/.lake/build/lib/lean'))))
imports=[m for line in data.decode().splitlines() if line.startswith('import ') for m in line[7:].split()]
def deps():
 out={}
 for m in imports:
  for base in [L/'objects',B/'build/objects']:
   op=base/pathlib.Path(*m.split('.')).with_suffix('.olean')
   if op.exists():out[m]={'path':str(op),'sha256':hashlib.sha256(op.read_bytes()).hexdigest()};break
 return out
before=deps();cmd=['timeout',str(limit),'lean','-j1','-M'+str(memory),'-o',str(frozen/f'{name}.olean'),p.name];t=time.monotonic()
with (frozen/f'{name}.log').open('w') as log:r=subprocess.run(cmd,cwd=frozen,env=env,stdout=log,stderr=subprocess.STDOUT)
text=(frozen/f'{name}.log').read_text();axioms=[' '.join(x.split()) for x in re.findall(r"'[^']+' depends on axioms: \[.*?\]|'[^']+' does not depend on any axioms",text,re.S)];bad=[]
for line in axioms:
 match=re.search(r'\[(.*?)\]',line)
 if match:bad += [a.strip() for a in match.group(1).split(',') if a.strip() not in ['propext','Classical.choice','Quot.sound']]
stable=before==deps();meta={'module':name,'status':'PASS_LOCAL_COMPONENT' if r.returncode==0 and stable and not bad else 'FAILED_ATTEMPT','exit_code':r.returncode,'command':cmd,'compile_cwd':str(frozen),'elapsed_seconds':time.monotonic()-t,'source_sha256':h,'source_matches_current_working_copy':hashlib.sha256(p.read_bytes()).hexdigest()==h,'compiler':'Lean4.33.1 Linux commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6','mathlib_commit':'0df444a360eaa60ab8c11dca51a86af692955474','direct_project_imports':before,'project_imports_stable_during_compile':stable,'axiom_lines':axioms,'nonstandard_axioms':bad,'log_sha256':hashlib.sha256(text.encode()).hexdigest(),'verified_snapshot':str(frozen)}
obj=frozen/f'{name}.olean'
if obj.exists():meta['olean_sha256']=hashlib.sha256(obj.read_bytes()).hexdigest()
(frozen/f'{name}-receipt.json').write_text(json.dumps(meta,indent=2)+'\n');(L/'receipts'/f'{name}-receipt.json').write_text(json.dumps(meta,indent=2)+'\n')
if meta['status']=='PASS_LOCAL_COMPONENT':
 (L/'objects').mkdir(exist_ok=True);shutil.copyfile(obj,L/'objects'/obj.name)
print(json.dumps(meta,indent=2));print(text)
