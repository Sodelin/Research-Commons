"""Experimental local final-call certificate engine for polynomial source models.

Every model has shared parameters across ALL deterministic row laws. Source
providers must certify model coverage/image equivalence separately. Quantifier
elimination remaining incomplete is UNKNOWN, not an identifying policy.
This module is excluded from both frozen reviewed releases.
"""
import time
import sympy as sp
import z3


def to_z3(expression, mapping):
    if expression.is_Rational:return z3.RealVal(str(expression))
    if expression.is_Symbol:return mapping[expression]
    if expression.is_Add:return sum((to_z3(v,mapping) for v in expression.args),z3.RealVal(0))
    if expression.is_Mul:
        out=z3.RealVal(1)
        for v in expression.args:out=out*to_z3(v,mapping)
        return out
    if expression.is_Pow and expression.exp.is_Integer and expression.exp>=0:
        return to_z3(expression.base,mapping)**int(expression.exp)
    raise ValueError('Only exact rational polynomial source laws are supported.')


def quantifier_present(expression):
    return z3.is_quantifier(expression) or any(quantifier_present(v) for v in expression.children())


def final_call_relation(models, weight_variables, weight_domain, history=None, milliseconds=5000):
    """Return a QF winning relation or honest UNKNOWN for one remaining call.

    History entries are (known row-weight vector, known response vector).
    Source parameters are freshly renamed per competitor and reused across its
    whole history. Action weights stay FREE during source-parameter QE.
    """
    history=history or []
    weights=weight_variables
    zweights={w:z3.Real(str(w)) for w in weights}
    constraints=[];receipts=[]
    for i,a in enumerate(models):
        for j,b in enumerate(models[i+1:],i+1):
            if a['target']==b['target']:continue
            avars=[sp.Symbol('sourceA_'+str(k)) for k in range(len(a['variables']))]
            bvars=[sp.Symbol('sourceB_'+str(k)) for k in range(len(b['variables']))]
            amap=dict(zip(a['variables'],avars));bmap=dict(zip(b['variables'],bvars))
            alaws=[[v.xreplace(amap) for v in row] for row in a['laws']]
            blaws=[[v.xreplace(bmap) for v in row] for row in b['laws']]
            sourcevars=avars+bvars;zsource={v:z3.Real(str(v)) for v in sourcevars};mapping={**zsource,**zweights}
            source_domain=z3.And(*[z3.And(zsource[v]>0,zsource[v]<1) for v in sourcevars])
            equations=[]
            for oldweights,response in history:
                for laws in (alaws,blaws):
                    equations.extend(sp.expand(sum(w*row[k] for w,row in zip(oldweights,laws))-response[k]) for k in range(len(response)))
            predictedA=[sp.expand(sum(w*row[k] for w,row in zip(weights,alaws))) for k in range(len(alaws[0]))]
            predictedB=[sp.expand(sum(w*row[k] for w,row in zip(weights,blaws))) for k in range(len(blaws[0]))]
            equations.extend(sp.expand(x-y) for x,y in zip(predictedA,predictedB))
            formula=z3.Exists(list(zsource.values()),z3.And(source_domain,weight_domain(zweights),*[to_z3(e,mapping)==0 for e in equations]))
            goal=z3.Goal();goal.add(formula);started=time.monotonic()
            try:reduced=z3.TryFor(z3.Tactic('qe'),milliseconds)(goal).as_expr()
            except z3.Z3Exception as e:
                return {'status':'UNKNOWN_QE_RESOURCE_LIMIT','completed_pairs':receipts,'reason':str(e)}
            if quantifier_present(reduced):
                return {'status':'UNKNOWN_PARTIAL_SOURCE_PARAMETER_QE','completed_pairs':receipts,'partial_relation':str(reduced)}
            constraints.append(z3.Not(reduced))
            receipts.append({'source_pair':[i,j],'different_target':True,'eliminated_relation':str(reduced),'elapsed_seconds':time.monotonic()-started})
    winning=z3.And(weight_domain(zweights),*constraints)
    return {'status':'QUANTIFIER_FREE_FINAL_CALL_RELATION','relation':winning,'weight_variables':zweights,'pair_receipts':receipts}
