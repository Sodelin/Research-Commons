#!/usr/bin/env python3
"""Independent positive-polynomial certificates and local final-call QE replay.

The source-image provider is the independently accepted complete n4/r1
full-forcing supplement. No recursive policy synthesis is inferred.
"""
from pathlib import Path
import itertools
import hashlib
import json
import time
import sympy as sp
import z3
from experimental_last_call_solver import final_call_relation


def main():
    root=Path(__file__).resolve().parent
    x0,x1,y0,y1,w0,w1=sp.symbols('sourceA0 sourceA1 sourceB0 sourceB1 programmeWeight0 programmeWeight1')
    sources=list(itertools.product(range(3),repeat=2))
    def row(target,s):return [1-2*s/3 if i==target else s/3 for i in range(3)]
    def response(targets,variables):return [sp.expand(w0*a+w1*b) for a,b in zip(row(targets[0],variables[0]),row(targets[1],variables[1]))]
    identities=[]
    for a,b in itertools.combinations(sources,2):
        A,B=set(a),set(b)
        if A==B:continue
        avars=[x0,x1];bvars=[y0,y1]
        equations=[sp.expand(p-q) for p,q in zip(response(a,avars),response(b,bvars))]
        onlyA,onlyB=A-B,B-A
        if onlyA:
            i=min(onlyA);j=min(onlyB) if onlyB else min(set(range(3))-(A|B));sign=1
        else:
            i=min(onlyB);j=min(set(range(3))-(A|B));sign=-1
        terms=[]
        if sign==1:
            terms.extend((weight,1-variable) for target,variable,weight in zip(a,avars,[w0,w1]) if target==i)
            terms.extend((weight,1-variable) for target,variable,weight in zip(b,bvars,[w0,w1]) if target==j)
        else:
            terms.extend((weight,1-variable) for target,variable,weight in zip(b,bvars,[w0,w1]) if target==i)
        positive_sum=sp.expand(sum(weight*bound for weight,bound in terms))
        if not terms or sp.expand(sign*(equations[i]-equations[j])-positive_sum)!=0:
            raise RuntimeError('Invalid universal positive identity for source pair '+str((a,b)))
        # Every factor is strictly positive under the declared source/action domain.
        if any(weight not in (w0,w1) or bound not in (1-x0,1-x1,1-y0,1-y1) for weight,bound in terms):
            raise RuntimeError('Unrecognized positive-factor rule.')
        identities.append({'source_imageA':a,'source_imageB':b,'equations':[str(p) for p in equations],
                           'coordinate_indices':[i,j],'orientation':sign,
                           'positive_products':[[str(weight),str(bound)] for weight,bound in terms],
                           'exact_identity_check':'PASS','strict_order_contradiction':'a nonempty sum of products of strictly positive factors cannot equal zero'})
    models=[];s,t=sp.symbols('survival0 survival1')
    for a,b in sources:models.append({'variables':[s,t],'laws':[row(a,s),row(b,t)],'target':tuple(sorted({a,b}))})
    start=time.monotonic()
    domain=lambda weights:z3.And(weights[w0]>0,weights[w1]>0,weights[w0]+weights[w1]==1)
    result=final_call_relation(models,[w0,w1],domain,milliseconds=3000)
    if result['status']!='QUANTIFIER_FREE_FINAL_CALL_RELATION':raise RuntimeError(result['status'])
    zweights=result['weight_variables'];equivalence=z3.SolverFor('QF_NRA');equivalence.add(z3.Xor(result['relation'],domain(zweights)))
    if equivalence.check()!=z3.unsat:raise RuntimeError('Final-call relation differs from the complete positive simplex.')
    receipt={'schema':'source-admitted-last-call-33-pair-all-interior-experiment-v1',
             'status':'PASS_INDEPENDENT_POSITIVE_IDENTITIES_AND_LOCAL_QE',
             'source_provider_manifest_sha256':'3c11ea185f573e6bf47d62a2dde96bd6215aa8eac4073b361f3571557793cbf1',
             'source_image_certificate_sha256':'2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8',
             'software':{'sympy':sp.__version__,'z3':z3.get_version_string()},
             'domain':{'source_parameters':'0<sourceA0,sourceA1,sourceB0,sourceB1<1',
                       'programme_weights':'programmeWeight0>0,programmeWeight1>0,sum=1'},
             'formulation':'For each different-target competitor pair, exclude existence of two jointly history-consistent source assignments with equal proposed responses. The final response vector is eliminated logically before source-parameter QE.',
             'history_in_this_experiment':[],
             'exact_positive_identity_certificates':identities,
             'quantifier_free_relation':str(z3.simplify(result['relation'])),
             'local_QE_pair_receipts':result['pair_receipts'],'elapsed_seconds':time.monotonic()-start,
             'trust':'The all-interior conclusion has an independent rational-polynomial/strict-order certificate; local QE is a separately replayed computational check.',
             'scope':'Accepted exact nine source images of all546 original n4/r1 full-forcing sources. No generic multi-call CAD, Lean, empirical or unknown-size claim.'}
    (root/'ALL-INTERIOR-EXPERIMENT-RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'independent_pair_certificates':len(identities),'z3':z3.get_version_string(),'elapsed_seconds':receipt['elapsed_seconds']},indent=2))


if __name__=='__main__':main()
