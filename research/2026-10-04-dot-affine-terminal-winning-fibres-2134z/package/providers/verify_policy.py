"""Verify a finite observation-dependent policy against shared source models.

This verifies a supplied policy. It does not synthesize one or infer catalogue
coverage. Complete actual source admission is a separately pinned provider.
Each completed universal obligation is checked by its existential QF_NRA
counterexample; trust remains SAME_BACKEND. Residual/resource failures UNKNOWN.
"""
import ast
import ctypes
import json
import z3
from terminal_engine import validate_models, validate_history, polynomial_to_z3

class PolicyEncodingError(ValueError):pass
class PolicyLimit(RuntimeError):pass

def expression(text, observed):
    if type(text) is int:text=str(text)
    if not isinstance(text,str):raise PolicyEncodingError('Exact expressions use integer/rational text, never floats.')
    def go(n,depth=0):
        if depth>64:raise PolicyLimit('Expression nesting exceeds the 64-level evaluation resource ceiling.')
        if isinstance(n,ast.Constant) and type(n.value) is int:return z3.RealVal(n.value),z3.BoolVal(True)
        if isinstance(n,ast.Name):
            if n.id not in observed:raise PolicyEncodingError('An action/guard can read only earlier observed response coordinates.')
            return observed[n.id],z3.BoolVal(True)
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):
            a,valid=go(n.operand,depth+1);return -a,valid
        if isinstance(n,ast.BinOp):
            a,av=go(n.left,depth+1);b,bv=go(n.right,depth+1);valid=z3.And(av,bv)
            if isinstance(n.op,ast.Add):return a+b,valid
            if isinstance(n.op,ast.Sub):return a-b,valid
            if isinstance(n.op,ast.Mult):return a*b,valid
            if isinstance(n.op,ast.Div):return a/b,z3.And(valid,b!=0)
            if isinstance(n.op,ast.Pow) and isinstance(n.right,ast.Constant) and type(n.right.value) is int and n.right.value>=0:return (z3.RealVal(1) if n.right.value==0 else a**n.right.value),valid
        raise PolicyEncodingError('Only exact rational arithmetic and nonnegative integer powers are supported.')
    return go(ast.parse(text,mode='eval').body)

def guard(value,observed,depth=0):
    if depth>64:raise PolicyLimit('Guard nesting exceeds the 64-level evaluation resource ceiling.')
    if type(value) is bool:return z3.BoolVal(value),z3.BoolVal(True)
    if not isinstance(value,dict) or 'op' not in value:raise PolicyEncodingError('Malformed semialgebraic guard.')
    op=value['op']
    if op in ('and','or') and set(value)=={'op','args'} and isinstance(value['args'],list):
        parts=[guard(p,observed,depth+1) for p in value['args']]
        result=(z3.And if op=='and' else z3.Or)(*[p[0] for p in parts])
        return result,z3.And(*[p[1] for p in parts])
    if op=='not' and set(value)=={'op','arg'}:
        a,defined=guard(value['arg'],observed,depth+1);return z3.Not(a),defined
    if op in ('eq','ne','lt','le','gt','ge') and set(value)=={'op','left','right'}:
        a,av=expression(value['left'],observed);b,bv=expression(value['right'],observed)
        values={'eq':a==b,'ne':a!=b,'lt':a<b,'le':a<=b,'gt':a>b,'ge':a>=b}
        return values[op],z3.And(av,bv)
    raise PolicyEncodingError('Unsupported guard fields/operator.')

def canonical_target(x):return json.dumps(x,sort_keys=True,separators=(',',':'))

def verify(models,policy,supports,row_sites,budget,initial_history=(),milliseconds=3000,max_nodes=10000):
    receipts=[];visited=0
    def query(formula,kind,source,path):
        solver=z3.SolverFor('QF_NRA');solver.set(timeout=milliseconds);solver.add(formula)
        result=solver.check();record={'kind':kind,'source_model':source,'policy_path':path,'status':str(result),'query_smt2':solver.to_smt2()}
        if result==z3.sat:record['counterexample_model']=str(solver.model())
        if result==z3.unknown:record['reason']=solver.reason_unknown()
        receipts.append(record)
        if result==z3.unknown:raise PolicyLimit('A required exact source obligation remained UNKNOWN.')
        return result
    def obligation(path_domain,condition,kind,source,path):
        if query(z3.And(path_domain,z3.Not(condition)),kind,source,path)!=z3.unsat:
            raise PolicyEncodingError('A reachable policy obligation failed: '+kind)
    try:
        k,q=validate_models(models)
        if not isinstance(budget,list) or len(budget)!=3 or any(type(n) is not int or n<0 for n in budget):raise PolicyEncodingError('Invalid PATH [calls,configurations,sites] budget.')
        if type(milliseconds) is not int or not 0<milliseconds<=60000 or type(max_nodes) is not int or max_nodes<1:raise PolicyEncodingError('Invalid resource limit.')
        # Preflight is iterative: deeply nested/cyclic user trees must not
        # reach Python or Z3's recursive binding before resource rejection.
        pending=[(policy,0)];preflight_nodes=0
        while pending:
            item,depth=pending.pop();preflight_nodes+=1
            if depth>128:raise PolicyLimit('Policy nesting exceeds the 128-level execution resource ceiling.')
            if preflight_nodes>max_nodes:raise PolicyLimit('Finite policy preflight exceeds max_nodes.')
            if isinstance(item,dict):
                if item.get('kind')=='call' and 'next' in item:pending.append((item['next'],depth+1))
                if item.get('kind')=='decision' and isinstance(item.get('branches'),list):
                    pending.extend((b['next'],depth+1) for b in item['branches'] if isinstance(b,dict) and 'next' in b)
        if len(row_sites)!=k or not all(isinstance(v,(set,list,tuple)) and all(isinstance(x,str) for x in v) for v in row_sites):raise PolicyEncodingError('Original row-site carrier mismatch.')
        if not isinstance(supports,list) or not supports or any(not s or len(s)!=len(set(s)) or any(type(i) is not int or not 0<=i<k for i in s) for s in supports):raise PolicyEncodingError('Unsupported action support menu.')
        allowed={tuple(sorted(s)) for s in supports};validate_history(initial_history,k,q,supports)
        old_rows=set();old_sites=set()
        for w,y in initial_history:
            chosen={i for i,v in enumerate(w) if v>0};old_rows|=chosen
            for i in chosen:old_sites|=set(row_sites[i])
        if len(initial_history)>budget[0] or len(old_rows)>budget[1] or len(old_sites)>budget[2]:raise PolicyEncodingError('Known history already exceeds PATH budget.')
        admitted=False
        for source,model in enumerate(models):
            symbols={v:z3.FreshReal('oneOriginalSourceParameter') for v in model['variables']}
            laws=[[polynomial_to_z3(v,symbols) for v in row] for row in model['laws']]
            domain=z3.And(*[z3.And(v>0,v<1) for v in symbols.values()]);observed={}
            for h,(weights,response) in enumerate(initial_history):
                wz=[polynomial_to_z3(v,{}) for v in weights];rz=[polynomial_to_z3(v,{}) for v in response]
                domain=z3.And(domain,*[sum(wz[i]*laws[i][j] for i in range(k))==rz[j] for j in range(q)])
                observed.update({f'h{h}_{j}':v for j,v in enumerate(rz)})
            feasible=query(domain,'initial_joint_history_admission',source,[])
            if feasible==z3.unsat:continue
            admitted=True
            def walk(node,path_domain,obs,calls,used_rows,used_sites,path):
                nonlocal visited
                visited+=1
                if visited>max_nodes:raise PolicyLimit('Finite policy expansion exceeds max_nodes.')
                if not isinstance(node,dict) or 'kind' not in node:raise PolicyEncodingError('Malformed policy node.')
                kind=node['kind']
                if kind=='leaf' and set(node)=={'kind','target'}:
                    obligation(path_domain,z3.BoolVal(canonical_target(node['target'])==canonical_target(model['target'])),'actual_target_leaf',source,path);return
                if kind=='decision' and set(node)=={'kind','branches'} and isinstance(node['branches'],list):
                    remaining=path_domain;parts=[]
                    for b,branch in enumerate(node['branches']):
                        if not isinstance(branch,dict) or set(branch)!={'guard','next'}:raise PolicyEncodingError('Malformed guarded branch.')
                        g,defined=guard(branch['guard'],obs)
                        obligation(remaining,defined,'guard_defined_on_reachable_history',source,path+[b])
                        active=z3.And(remaining,g);parts.append(g)
                        walk(branch['next'],active,obs,calls,used_rows,used_sites,path+[b])
                        # A finite deterministic first-eligible convention is
                        # applied; later guards cannot steal earlier histories.
                        remaining=z3.And(remaining,z3.Not(g))
                    obligation(path_domain,z3.Or(*parts),'complete_reachable_response_coverage',source,path);return
                if kind=='call' and set(node)=={'kind','support','weights','next'}:
                    support=node['support']
                    if not isinstance(support,list) or any(type(i) is not int for i in support) or tuple(sorted(support)) not in allowed or len(support)!=len(set(support)):raise PolicyEncodingError('Policy action uses an unsupported support.')
                    if not isinstance(node['weights'],list) or len(node['weights'])!=k:raise PolicyEncodingError('Policy action cannot truncate the original row carrier.')
                    expressions=[expression(v,obs) for v in node['weights']];weights=[v for v,d in expressions]
                    legal=z3.And(*[d for v,d in expressions],sum(weights)==1,
                                 *[weights[i]>0 if i in support else weights[i]==0 for i in range(k)])
                    obligation(path_domain,legal,'source_reachable_real_action_legality',source,path)
                    rows=used_rows|set(support);sites=used_sites|set().union(*(set(row_sites[i]) for i in support))
                    cost=z3.BoolVal(calls+1<=budget[0] and len(rows)<=budget[1] and len(sites)<=budget[2])
                    obligation(path_domain,cost,'PATH_union_resource_budget',source,path)
                    response=[z3.simplify(sum(weights[i]*laws[i][j] for i in range(k))) for j in range(q)]
                    nxt={**obs,**{f'h{calls}_{j}':v for j,v in enumerate(response)}}
                    # The SAME symbols/laws persist; no history refitting and
                    # no free response chosen existentially by the verifier.
                    walk(node['next'],path_domain,nxt,calls+1,rows,sites,path+['call']);return
                raise PolicyEncodingError('Unknown policy kind or unexpected fields.')
            walk(policy,domain,observed,len(initial_history),old_rows,old_sites,[])
        if not admitted:
            return {'status':'NO_ADMITTED_SOURCE_FOR_INITIAL_HISTORY_SAME_BACKEND','receipts':receipts,'policy_verified':False}
        return {'status':'FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND','receipts':receipts,
                'source_models':len(models),'policy_nodes_checked':visited,'path_budget':budget,
                'source_assignment_shared_through_complete_history':True,
                'coverage':'all source-generated reachable response histories, with deterministic first-eligible guards',
                'trust':'completed exact Z3 QF_NRA counterexample checks; no independent generic proof replay',
                'source_admission':'separate complete original-source provider required',
                'generic_adaptive_policy_synthesis_claimed':False}
    except (PolicyLimit,RecursionError,ctypes.ArgumentError) as e:
        return {'status':'UNKNOWN_POLICY_VERIFICATION_RESOURCE_LIMIT','reason':str(e),'receipts':receipts,'policy_verified':False}
    except (ValueError,TypeError,KeyError,AttributeError,SyntaxError,z3.Z3Exception) as e:
        return {'status':'INVALID_OR_REFUTED_POLICY','reason':str(e),'receipts':receipts,'policy_verified':False}
