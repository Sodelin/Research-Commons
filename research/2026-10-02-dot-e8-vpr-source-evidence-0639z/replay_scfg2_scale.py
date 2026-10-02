"""Exercise existing public adapter fixtures across its public scale override."""
import ast, hashlib, json, math, os, pathlib, subprocess, time
BASE = pathlib.Path(__file__).resolve().parent
SRC = BASE/'scfg2-replay-source'
BIN = BASE/'scfg2-replay-build/scfg2_exact_adapter'
PARAM = SRC/'submodules/CParty/params/rna_DirksPierce09.par'
public_test = ast.parse((SRC/'tests/test_scfg2_exact_adapter.py').read_text())
const = {}
for node in public_test.body:
    if isinstance(node, ast.Assign) and isinstance(node.targets[0], ast.Name):
        name = node.targets[0].id
        if name in ('SEQUENCE', 'SCAFFOLD', 'TARGET', 'VP_BORDER_CASES'):
            const[name] = ast.literal_eval(node.value)
fixtures = [('public22',const['SEQUENCE'],const['SCAFFOLD'],const['TARGET']),
            ('public22_empty',const['SEQUENCE'],const['SCAFFOLD'],'.'*len(const['SEQUENCE']))]
fixtures += [tuple(x[:4]) for x in const['VP_BORDER_CASES']]
fixtures += [('nested9_empty','GGGAAACCC','.........','.........')]
records = []
for name,seq,g,target in fixtures:
    for scale in ('default','1','1.05','1.2','1.5','2'):
        env = dict(os.environ)
        env.pop('CPARTY_PF_OVERRIDE_SCALE',None)
        env.pop('CPARTY_PF_EXACT_W_PREFIX_SCALE_SEED',None)
        if scale != 'default': env['CPARTY_PF_OVERRIDE_SCALE'] = scale
        for mode in ('probability','energy'):
            cmd = [str(BIN),mode,seq,g,target,str(PARAM)]
            start=time.monotonic()
            r=subprocess.run(cmd,env=env,capture_output=True,text=True,timeout=20)
            first=r.stdout.split('\t')[0].strip()
            try: value=float(first)
            except ValueError:value=None
            records.append({'fixture':name,'n':len(seq),'scale':scale,'mode':mode,'returncode':r.returncode,
                            'value':value,'stdout':r.stdout,'stderr':r.stderr,'seconds':time.monotonic()-start})
    rows=[r for r in records if r['fixture']==name]
    print(json.dumps({'fixture':name,'records':len(rows),'failures':sum(r['returncode']!=0 for r in rows),
                      'energies':[r['value'] for r in rows if r['mode']=='energy'],
                      'log_probabilities':[r['value'] for r in rows if r['mode']=='probability']}),flush=True)
summary=[]
for name,seq,g,target in fixtures:
    group=[r for r in records if r['fixture']==name]
    item={'fixture':name,'n':len(seq),'sequence':seq,'scaffold':g,'target':target}
    for mode in ('probability','energy'):
        vals=[r['value'] for r in group if r['mode']==mode and r['returncode']==0 and r['value'] is not None and math.isfinite(r['value'])]
        item[mode+'_finite_count']=len(vals)
        item[mode+'_range']=max(vals)-min(vals) if vals else None
    summary.append(item)
receipt={'pin':'27afdd054272dbda8a74c8aad156970a44c23cd8','binary_sha256':hashlib.sha256(BIN.read_bytes()).hexdigest(),
         'parameter_sha256':hashlib.sha256(PARAM.read_bytes()).hexdigest(),'scales':['default','1','1.05','1.2','1.5','2'],
         'records':records,'summary':summary,'evidence_kind':'independently executed public-source fixed-fixture scale replay; not formal numeric proof'}
(BASE/'SCFG2-SCALE-REPLAY.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps({'calls':len(records),'summary':summary},indent=2))
