"""Same-contract comparison of a checked import and one inline expansion."""
from pathlib import Path
import json, os, statistics, subprocess, sys, tempfile, time
lean=Path(sys.argv[1]).resolve(strict=True)
root=Path(__file__).resolve().parent
grid=(root/'CappedGridCross.lean').read_text()
branch=(root/'BranchBagProjection.lean').read_text()
# The inline comparison reuses the same mathematical argument, not a second
# independent discovery attempt. Only the module boundary is varied.
gridbody=grid.split('namespace ResearchCommons.CappedGridCross\n',1)[1].split('end ResearchCommons.CappedGridCross',1)[0]
body=branch.split('namespace ResearchCommons.BranchBagProjection\n',1)[1].split('-- Collisions',1)[0]
body=body.replace('open ResearchCommons.CappedGridCross\n','',1)
inline='import Lean\nnamespace AuditInline\n'+gridbody+body+'\n#print axioms width_from_branch_hits\nend AuditInline\n'
reuse=branch.split('-- Collisions',1)[0]+'\n#print axioms width_from_branch_hits\nend ResearchCommons.BranchBagProjection\n'
times={'inline':[],'reuse_prebuilt':[],'reuse_fresh':[]}
def run(cwd,*args):
    env=dict(os.environ,LEAN_PATH=str(cwd))
    p=subprocess.run([str(lean),*args],cwd=cwd,env=env,check=True,text=True,capture_output=True,timeout=30)
    assert 'sorryAx' not in p.stdout
    return p.stdout
def timed(fn):
    t=time.monotonic()
    out=fn()
    return time.monotonic()-t,out
with tempfile.TemporaryDirectory(prefix='pb_projection_audit_') as tmp:
    d=Path(tmp)
    for n,s in [('CappedGridCross',grid),('Inline',inline),('Reuse',reuse)]: (d/(n+'.lean')).write_text(s)
    for i in range(5):
        def fresh():
            run(d,'-o','CappedGridCross.olean','CappedGridCross.lean')
            return run(d,'Reuse.lean')
        if i%2==0:
            u,ui=timed(lambda:run(d,'Inline.lean'))
            c,ri=timed(fresh)
        else:
            c,ri=timed(fresh)
            u,ui=timed(lambda:run(d,'Inline.lean'))
        w,wi=timed(lambda:run(d,'Reuse.lean'))
        assert ui.split('depends on axioms: ')[-1]==ri.split('depends on axioms: ')[-1]==wi.split('depends on axioms: ')[-1]
        for k,x in [('inline',u),('reuse_fresh',c),('reuse_prebuilt',w)]:times[k].append(x)
    # The independent check below imports both variants and fixes one common exact type.
    run(d,'-o','Inline.olean','Inline.lean')
    run(d,'-o','Reuse.olean','Reuse.lean')
    (d/'Contract.lean').write_text('''import Inline
import Reuse
set_option warningAsError true
def Target : Prop :=
  ∀ {V : Type} (n : Nat) (bag : List V) (cellOf : V → Option (Nat × Nat)),
    (∀ i j, i < n → j < n →
      ∃ v ∈ bag, ∃ x, cellOf v = some x ∧ (x.1 = i ∨ x.2 = j)) → n ≤ bag.length
example : Target := @AuditInline.width_from_branch_hits
example : Target := @ResearchCommons.BranchBagProjection.width_from_branch_hits
''')
    run(d,'Contract.lean')
out={'schema':'commons.proofbridge.projection_ablation.v1',
     'elapsed':{k:{'trials_seconds':[round(x,3) for x in a],'median_seconds':round(statistics.median(a),3)} for k,a in times.items()},
     'nonblank_source_lines':{'inline':sum(bool(l.strip()) for l in inline.splitlines()),'reuse_consumer':sum(bool(l.strip()) for l in reuse.splitlines())},
     'one_exact_contract_checked_by_independent_consumer':True,'same_axiom_report':True,
     'limits':'One inline expansion of the same argument, not independently drafted proofs or a measurement of authoring hours.'}
print(json.dumps(out,indent=2))
