"""Compile complete target guards from an observation-dependent action word.

This is exact symbolic projection of jointly affine source-parameter laws,
followed by source-derived rank coverage and whole-policy verification. Failure
is UNKNOWN, not a budget NO. Action search/general nonlinear projection pending.
"""
import itertools
import ctypes
import json
import sympy as sp
import z3
from verify_policy import expression,verify
from terminal_engine import validate_models,polynomial_to_z3

def polynomial(text,names):
    # Reuse the independent safe grammar, with exact SymPy arithmetic only.
    import ast
    def go(n,depth=0):
        if depth>64:raise ValueError('Action-expression nesting resource ceiling64 exceeded; projection UNKNOWN.')
        if isinstance(n,ast.Constant) and type(n.value) is int:return sp.Integer(n.value)
        if isinstance(n,ast.Name) and n.id in names:return names[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -go(n.operand,depth+1)
        if isinstance(n,ast.BinOp):
            a,b=go(n.left,depth+1),go(n.right,depth+1)
            if isinstance(n.op,ast.Add):return a+b
            if isinstance(n.op,ast.Sub):return a-b
            if isinstance(n.op,ast.Mult):return a*b
            if isinstance(n.op,ast.Div):return a/b
            if isinstance(n.op,ast.Pow) and b.is_Integer and b>=0:return a**b
        raise ValueError('Action reads an unencoded or nonhistorical expression.')
    return go(ast.parse(text,mode='eval').body)

def relation(op,left,right=0):return {'op':op,'left':str(left),'right':str(right)}

def canonical_source_models(models):
    """Capture-avoiding typed source identities; caller spellings are metadata.

    Dummy identity, rather than a reserved spelling, keeps even legal source
    names such as h0_0 distinct from observations and generated auxiliaries.
    """
    canonical=[];provenance=[]
    for owner,model in enumerate(models):
        renaming={v:sp.Dummy(f'g7Source_model{owner}_parameter{i}')
                  for i,v in enumerate(model['variables'])}
        canonical.append({**model,'variables':[renaming[v] for v in model['variables']],
                          'laws':[[v.xreplace(renaming) for v in row] for row in model['laws']]})
        provenance.append({'source_model':owner,'parameters':[
            {'original_name':str(v),'typed_identity':f'source:{owner}:{i}',
             'display_name':str(renaming[v])} for i,v in enumerate(model['variables'])]})
    return canonical,provenance

def compile_policy(models,calls,supports,row_sites,budget,milliseconds=3000,max_minors=100):
    receipts=[];regions={};targets={}
    try:
        k,q=validate_models(models)
        original_models=models
        models,source_provenance=canonical_source_models(models)
        if type(milliseconds) is not int or not 0<milliseconds<=60000 or type(max_minors) is not int or max_minors<1:raise ValueError('Invalid projection resource limit.')
        if not isinstance(calls,list) or len(calls)>128:raise ValueError('Finite action-word resource ceiling128 exceeded; projection UNKNOWN.')
        if not calls:raise ValueError('This affine decoder requires an actual nonempty action word.')
        for source,model in enumerate(models):
            names={};equations=[];actual={};public_history={}
            for step,call in enumerate(calls):
                if not isinstance(call,dict) or set(call)!={'support','weights'} or len(call['weights'])!=k:raise ValueError('Action word carrier/fields mismatch.')
                weights=[polynomial(v,names) for v in call['weights']]
                # Observations remain symbolic in inverse equations, while a
                # separate exact forward substitution retains one source point.
                forward_weights=[v.subs(actual) for v in weights]
                for j in range(q):
                    public_name=f'h{step}_{j}'
                    h=sp.Dummy(f'g7History_step{step}_coordinate{j}')
                    prediction=sum(weights[i]*model['laws'][i][j] for i in range(k))
                    equations.append(sp.together(prediction-h))
                    actual[h]=sp.cancel(sum(forward_weights[i]*model['laws'][i][j] for i in range(k)))
                    names[public_name]=h
                    public_history[h]=sp.Symbol(public_name)
            # Clear only observation-dependent denominators, and retain their
            # nonzero guards. Source-dependent denominators are unsupported.
            numerators=[];denominators=[]
            for e in equations:
                num,den=sp.fraction(sp.cancel(e))
                if den.free_symbols & set(model['variables']):raise ValueError('Source-dependent rational law denominator.')
                numerators.append(num);denominators.append(den)
            A,b=sp.linear_eq_to_matrix(numerators,model['variables'])
            n=len(model['variables'])
            if not n:raise ValueError('Constant source models need the ordinary projection adapter.')
            if len(equations)<n:raise ValueError('Source parameters are underdetermined by the word; general QE required.')
            point={v:z3.FreshReal('sameOriginalSourceForRank') for v in model['variables']}
            domain=z3.And(*[z3.And(v>0,v<1) for v in point.values()])
            chosen=None;attempts=0
            for rows in itertools.combinations(range(A.rows),n):
                attempts+=1
                if attempts>max_minors:raise ValueError('Affine-minor search resource limit; no completeness NO.')
                square=A[list(rows),:];det=sp.factor(square.det())
                if det==0:continue
                # The original source word must NEVER enter a omitted singular
                # pivot cell. A completed QF_NRA counterexample check proves it.
                forward_det=sp.cancel(det.subs(actual));forward_den=[sp.cancel(d.subs(actual)) for d in denominators]
                def nz(v):
                    num,den=sp.fraction(v)
                    return z3.And(polynomial_to_z3(num,point)!=0,polynomial_to_z3(den,point)!=0)
                safe=z3.And(nz(forward_det),*[nz(d) for d in forward_den])
                solver=z3.SolverFor('QF_NRA');solver.set(timeout=milliseconds);solver.add(domain,z3.Not(safe));result=solver.check()
                receipts.append({'source_model':source,'minor_rows':list(rows),'determinant':str(det),'status':str(result),'query_smt2':solver.to_smt2()})
                if result==z3.unknown:raise ValueError('UNKNOWN original-source rank-coverage query.')
                if result==z3.unsat:chosen=(rows,square,det);break
            if chosen is None:raise ValueError('No one source-complete affine pivot; piecewise-rank/general QE adapter required.')
            rows,square,det=chosen;solution=square.inv()*b[list(rows),:];substitution=dict(zip(model['variables'],solution))
            def public_relation(op,left,right=0):
                left=sp.sympify(left);right=sp.sympify(right)
                if not (left.free_symbols|right.free_symbols)<=set(public_history):
                    raise ValueError('Uneliminated source or auxiliary identity in generated observation guard.')
                return relation(op,left.xreplace(public_history),right.xreplace(public_history))
            guards=[public_relation('ne',det)]+[public_relation('ne',d) for d in denominators]
            for v in solution:guards.extend([public_relation('gt',sp.cancel(v)),public_relation('lt',sp.cancel(v),1)])
            for e in equations:
                residual=sp.cancel(e.subs(substitution));num,den=sp.fraction(residual)
                guards.extend([public_relation('ne',den),public_relation('eq',num)])
            key=json.dumps(model['target'],sort_keys=True,separators=(',',':'));targets[key]=model['target'];regions.setdefault(key,[]).append({'op':'and','args':guards})
        tree={'kind':'decision','branches':[{'guard':{'op':'or','args':regions[key]},'next':{'kind':'leaf','target':targets[key]}} for key in sorted(regions)]}
        for call in reversed(calls):tree={'kind':'call','support':call['support'],'weights':call['weights'],'next':tree}
        checked=verify(original_models,tree,supports,row_sites,budget,milliseconds=milliseconds)
        if checked['status']!='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND':
            return {'status':'UNKNOWN_OR_REFUTED_COMPILED_CANDIDATE','rank_receipts':receipts,'verification':checked,'policy':tree}
        return {'status':'WHOLE_ACTION_WORD_TARGET_DECODER_COMPILED_AND_VERIFIED_SAME_BACKEND',
                'policy':tree,'rank_receipts':receipts,'verification':checked,
                'source_shared_parameters':True,'complete_reachable_response_coverage':True,
                'symbol_identity_provenance':{'method':'typed Dummy identities; simultaneous capture-avoiding xreplace',
                    'sources':source_provenance,'history':'history:step:coordinate; printed as hSTEP_COORD only after source elimination',
                    'actions':'observation-only parsed expressions; unbound action/source names rejected as UNKNOWN',
                    'auxiliaries':'independent Z3 FreshReal identities for rank and final verification'},
                'method':'source-complete affine inversion plus every residual/domain guard; whole policy reverified',
                'generic_action_search_or_nonlinear_QE_completion_claimed':False}
    except (ValueError,TypeError,KeyError,AttributeError,SyntaxError,RecursionError,ctypes.ArgumentError,sp.PolynomialError,z3.Z3Exception) as e:
        return {'status':'UNKNOWN_UNSUPPORTED_OR_INCOMPLETE_LEAF_COMPILATION','reason':str(e),'rank_receipts':receipts,'budget_NO_claimed':False}
