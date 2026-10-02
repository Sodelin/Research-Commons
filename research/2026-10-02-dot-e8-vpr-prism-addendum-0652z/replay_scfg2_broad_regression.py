"""Bounded fixed-seed source regression, not an all-input proof."""
import hashlib, json, math, os, pathlib, random, subprocess
P=pathlib.Path(__file__).resolve().parent
R=random.Random(20261002)
param=P/'scfg2-replay-source/submodules/CParty/params/rna_DirksPierce09.par'
fixtures=json.loads((P/'SCFG2-SCALE-REPLAY.json').read_text())['summary']
def pairs(s):
    stacks={c:[] for c in '([{<'}; closing=dict(zip(')]}>','([{<')); out=[]
    for i,c in enumerate(s):
        if c in stacks:stacks[c].append(i)
        elif c in closing:
            op=closing[c]
            if not stacks[op]:raise ValueError('unbalanced output')
            out.append((stacks[op].pop(),i))
        elif c!='.':raise ValueError('unexpected output character')
    if any(stacks.values()):raise ValueError('unclosed output')
    return sorted(out)
cases=[]
for f in fixtures:
    if f['fixture'] not in ('PKB436','PKB00048'):continue
    fixed={x for a in pairs(f['scaffold']) for x in a}
    for k in range(6):
        seq=list(f['sequence'])
        for i in range(len(seq)):
            if i not in fixed and R.random()<0.22:seq[i]=R.choice('ACGU')
        cases.append({'name':f['fixture']+'-mutant'+str(k),'sequence':''.join(seq),'scaffold':f['scaffold']})
for scaf in ['((....))....((....))....((....))....','((..((....))..((....))..))........']:
    for k in range(6):
        seq=[R.choice('ACGU') for _ in scaf]
        for i,j in pairs(scaf):seq[i],seq[j]=R.choice([('G','C'),('C','G'),('A','U'),('U','A')])
        cases.append({'name':'branched'+str(len(cases)),'sequence':''.join(seq),'scaffold':scaf})
rows=[]
for case in cases:
    n=len(case['sequence']);target='.'*n
    for variant in ['scfg2_exact_adapter','scfg2_vpr_hypothesis_adapter']:
        b=P/'scfg2-replay-build'/variant
        for scale in ['1','2']:
            env=dict(os.environ);env['CPARTY_PF_OVERRIDE_SCALE']=scale;env.pop('CPARTY_PF_EXACT_W_PREFIX_SCALE_SEED',None)
            q=subprocess.run([str(b),'probability',case['sequence'],case['scaffold'],target,str(param)],env=env,capture_output=True,text=True,timeout=12)
            try:v=float(q.stdout.strip())
            except ValueError:v=None
            rows.append({'case':case['name'],'variant':variant,'mode':'probability','scale':scale,'returncode':q.returncode,'value':v,'stdout':q.stdout,'stderr':q.stderr})
        q=subprocess.run([str(b),'viterbi',case['sequence'],case['scaffold'],str(param)],env=env,capture_output=True,text=True,timeout=12)
        fields=q.stdout.strip().split('\t');row={'case':case['name'],'variant':variant,'mode':'viterbi','scale':'2','returncode':q.returncode,'stdout':q.stdout,'stderr':q.stderr}
        if q.returncode==0 and len(fields)==3:
            generated=pairs(fields[2]);gp=pairs(case['scaffold']);row['generated_crossings']=[(a,b) for a in generated for b in generated if a[0]<b[0]<a[1]<b[1]];row['union_pair_identity']=pairs(fields[0])==sorted(gp+generated)
        rows.append(row)
summary=[]
for variant in ['scfg2_exact_adapter','scfg2_vpr_hypothesis_adapter']:
    vr=[x for x in rows if x['variant']==variant];delta=[]
    for c in cases:
        rr=[x for x in vr if x['case']==c['name'] and x['mode']=='probability']
        if all(x['returncode']==0 and x['value'] is not None and math.isfinite(x['value']) for x in rr):delta.append((c['name'],abs(rr[1]['value']-rr[0]['value'])))
    summary.append({'variant':variant,'calls':len(vr),'unexpected_process_failures':sum(x['returncode']!=0 for x in vr),'max_finite_scale_log_discrepancy':max(delta,key=lambda x:x[1]) if delta else None,'generated_crossing_cases':[x['case'] for x in vr if x.get('generated_crossings')],'union_identity_failures':[x['case'] for x in vr if x.get('union_pair_identity') is False]})
receipt={'seed':20261002,'pin':'27afdd054272dbda8a74c8aad156970a44c23cd8','cases':cases,'records':rows,'summary':summary,'target':'empty generated map for scale checks; public Viterbi output for support screen','scope':'bounded regression, not all-input energy/support proof'}
(P/'SCFG2-BROAD-REGRESSION.json').write_text(json.dumps(receipt,indent=2));print(json.dumps({'cases':len(cases),'calls':len(rows),'summary':summary},indent=2))
