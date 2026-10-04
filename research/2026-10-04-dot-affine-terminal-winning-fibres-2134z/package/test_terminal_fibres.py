#!/usr/bin/env python3
"""Compare complete projected terminal fibres to the direct pair predicate."""
import copy,json,time
from pathlib import Path
import sympy as sp
import z3
from provider_models import models
from terminal_fibres import compile_terminal_fibre
from terminal_engine import polynomial_to_z3
from verify_policy import guard,expression
ROOT=Path(__file__).resolve().parent
def direct(models,calls,observations,weights):
    def world(model):
        symbols={v:z3.FreshReal('oneWorldParameter') for v in model['variables']}
        rows=[[polynomial_to_z3(v,symbols) for v in row] for row in model['laws']]
        conditions=[z3.And(v>0,v<1) for v in symbols.values()];scope={}
        for step,(call,response) in enumerate(zip(calls,observations)):
            values=[expression(v,scope) for v in call['weights']]
            conditions.extend(d for v,d in values)
            for j,observed in enumerate(response):conditions.append(sum(v*rows[i][j] for i,(v,d) in enumerate(values))==z3.RealVal(str(observed)))
            scope.update({f'h{step}_{j}':z3.RealVal(str(v)) for j,v in enumerate(response)})
        return rows,conditions
    worlds=[world(m) for m in models]
    solver=z3.SolverFor('QF_LRA');solver.set(timeout=3000)
    solver.add(z3.Or(*[z3.And(*c) for rows,c in worlds]));admitted=solver.check()
    assert admitted!=z3.unknown
    collisions=[]
    for i,(ar,ac) in enumerate(worlds):
        for j in range(i+1,len(models)):
            if models[i]['target']==models[j]['target']:continue
            br,bc=worlds[j]
            collisions.append(z3.And(*ac,*bc,*[sum(z3.RealVal(str(w))*(ar[r][q]-br[r][q]) for r,w in enumerate(weights))==0 for q in range(len(ar[0]))]))
    solver=z3.SolverFor('QF_LRA');solver.set(timeout=3000);solver.add(z3.Or(*collisions));bad=solver.check();assert bad!=z3.unknown
    return admitted==z3.sat and bad==z3.unsat
def projected(result,history,actions):
    scope={f'h{i}_{j}':z3.RealVal(str(v)) for i,row in enumerate(history) for j,v in enumerate(row)}
    scope.update({f'a0_{i}':z3.RealVal(str(v)) for i,v in enumerate(actions)})
    g,defined=guard(result['winning_relation'],scope)
    assert z3.is_true(z3.simplify(defined))
    g=z3.simplify(g);assert z3.is_true(g) or z3.is_false(g)
    return z3.is_true(g)
def save(name,result):
    (ROOT/name).write_text(json.dumps(result,indent=2)+'\n')
def run():
    started=time.monotonic();sources=models();calls=[{'support':[0],'weights':['1','0']}];site=[['H0'],['H0']]
    full=compile_terminal_fibre(sources,calls,[0,1],site,[2,2,1]);assert full['status']=='TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED',full
    endpoint=compile_terminal_fibre(sources,calls,[1],site,[2,2,1]);assert endpoint['status']=='TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED',endpoint
    repeated=compile_terminal_fibre(sources,calls,[0],site,[2,2,1]);assert repeated['status']=='TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED',repeated
    save('ACTUAL-FULL-SUPPORT-TERMINAL-FIBRE.json',full);save('ACTUAL-ENDPOINT-TERMINAL-FIBRE.json',endpoint);save('ACTUAL-REPEATED-FORCE-TERMINAL-FIBRE.json',repeated)
    star=[[sp.Rational(1,3)]*3]
    assert not projected(full,star,[sp.Rational(1,2)]) and not direct(sources,calls,star,[sp.Rational(1,2)]*2)
    histories=[]
    for a in range(3):
        for s in (sp.Rational(1,4),sp.Rational(1,2),sp.Rational(3,4)):
            histories.append([[1-2*s/3 if j==a else s/3 for j in range(3)]])
    checks=[]
    for h in histories:
        for w in (sp.Rational(1,4),sp.Rational(1,2),sp.Rational(3,4)):
            expected=direct(sources,calls,h,[w,1-w]);value=projected(full,h,[w]);assert value==expected and value
            checks.append({'kind':'actual_interior','history':[[str(v) for v in row] for row in h],'weight':str(w),'winner':value})
        for name,relation,weights,expected in [('other_original_force',endpoint,[0,1],True),('same_original_force',repeated,[1,0],False)]:
            actual=direct(sources,calls,h,weights);value=projected(relation,h,[]);assert value==actual==expected
            checks.append({'kind':name,'history':[[str(v) for v in row] for row in h],'winner':value})
    # An independently initialized rival shares its own parameters through
    # BOTH repeated rows. Separately refitting those rows would admit this.
    calls2=calls+calls;two=compile_terminal_fibre(sources,calls2,[1],site,[3,2,1]);assert two['status']=='TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED',two
    impossible=[[sp.Rational(2,3),sp.Rational(1,6),sp.Rational(1,6)],[sp.Rational(1,2),sp.Rational(1,4),sp.Rational(1,4)]]
    assert not direct(sources,calls2,impossible,[0,1]) and not projected(two,impossible,[])
    save('REPEATED-HISTORY-SHARING-RELATION.json',two)
    # A rational action simplifies to a deterministic repetition, but its
    # original written denominator still excludes the h0_0=1/2 stratum.
    domain_calls=calls+[{'support':[0],'weights':['(h0_0-1/2)/(h0_0-1/2)','0']}]
    written=compile_terminal_fibre(sources,domain_calls,[1],site,[3,2,1]);assert written['status']=='TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED',written
    forbidden=[[sp.Rational(1,2),sp.Rational(1,4),sp.Rational(1,4)]]*2
    permitted=[[sp.Rational(2,3),sp.Rational(1,6),sp.Rational(1,6)]]*2
    assert not projected(written,forbidden,[]) and not direct(sources,domain_calls,forbidden,[0,1])
    assert projected(written,permitted,[]) and direct(sources,domain_calls,permitted,[0,1])
    save('WRITTEN-DENOMINATOR-TERMINAL-FIBRE.json',written)
    # Abstract encoding control with a genuine rank-zero conditional fibre.
    # The caller's source spelling collides with an observed/action spelling;
    # typed Dummy identity must preserve all equations nevertheless.
    x,y=sp.symbols('h0_0 a0_0')
    abstract=[{'variables':[x],'laws':[[x,1-x],[1-x,x]],'target':'A'},
              {'variables':[y],'laws':[[y,1-y],[y,1-y]],'target':'B'}]
    rank=compile_terminal_fibre(abstract,calls,[0,1],[[],[]],[2,2,0]);assert rank['status']=='TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED',rank
    for h in (sp.Rational(1,4),sp.Rational(1,2),sp.Rational(3,4)):
        for w in (sp.Rational(1,4),sp.Rational(1,2),sp.Rational(3,4)):
            expected=h!=sp.Rational(1,2);assert projected(rank,[[h,1-h]],[w])==direct(abstract,calls,[[h,1-h]],[w,1-w])==expected
            checks.append({'kind':'abstract_rank_zero_namespace_control','observed':str(h),'weight':str(w),'winner':expected})
    save('ABSTRACT-RANK-ZERO-TERMINAL-FIBRE.json',rank)
    negatives=[]
    def unknown(name,m=sources,c=calls,s=[0,1],rs=site,b=[2,2,1],**limits):
        out=compile_terminal_fibre(m,c,s,rs,b,**limits);assert out['status'].startswith('UNKNOWN_'),(name,out)
        negatives.append({'name':name,'status':out['status'],'reason':out.get('reason')})
    unknown('malformed_empty_carrier',[{'variables':[],'laws':[],'target':'x'}])
    unknown('unparsed_source_text',[{'variables':[x],'laws':[['__import__("os")',1]],'target':'x'}])
    with_domain=copy.deepcopy(sources);with_domain[0]['domain']='source-tied non-cube constraint';unknown('unsupported_extra_source_domain',with_domain)
    unknown('negative_probability_model',[{'variables':[x],'laws':[[-x,1+x],[-x,1+x]],'target':'x'}])
    bad=copy.deepcopy(sources);bad[0]['laws'][0]=[x*x,1-x*x,sp.Integer(0)];bad[0]['variables']=[x]
    unknown('jointly_nonlinear_source',bad)
    unknown('hidden_action_parameter',c=[{'support':[0,1],'weights':['sameOriginalSurvival0','1-sameOriginalSurvival0']}])
    unknown('undefined_written_domain',c=[{'support':[0,1],'weights':['(1/(h0_0-h0_0))**0','0']}])
    unknown('missing_action_row',c=[{'support':[0],'weights':['1']}])
    unknown('invalid_runtime',seconds=0)
    unknown('genuine_sign_partition_resource',m=abstract,c=[],rs=[[],[]],b=[1,2,0],max_branches=1)
    notaffordable=compile_terminal_fibre(sources,calls,[0,1],site,[1,2,1]);assert notaffordable['status']=='PROPOSED_SUPPORT_NOT_PATH_AFFORDABLE'
    negatives.append({'name':'local_path_affordability','status':notaffordable['status'],'global_budget_NO_claimed':False})
    result={'status':'PASS_AFFINE_TERMINAL_FIBRE_DIRECT_COMPARISONS','checks':checks,'additional_repeated_history_contradiction':True,'written_denominator_thin_stratum_retained':True,'inadmissible_uniform_first_history_rejected':True,'negative_controls':negatives,'seconds':time.monotonic()-started,
            'trust':'Direct QF_LRA point comparisons against separately built same-source pair predicates; no generic independent FM certificate or source-census proof'}
    save('TERMINAL-FIBRE-CONTROLS.json',result)
    print(json.dumps({'status':result['status'],'direct_point_comparisons':len(checks),'negative_controls':len(negatives),'seconds':result['seconds']}))
if __name__=='__main__':run()
