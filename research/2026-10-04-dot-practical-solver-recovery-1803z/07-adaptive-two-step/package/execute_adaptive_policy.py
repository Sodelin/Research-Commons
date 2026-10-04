#!/usr/bin/env python3
"""Execute the exact rational interface of a source-certified real adaptive policy."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'sourcekit'))
from solver import prepare_request, verify_witness, graph_json, target_json, physical_realization
from check_forced_pair_policy import witness

PROVIDER = '2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8'

def vector(values):
    if not isinstance(values, list) or len(values) != 3:
        raise ValueError('A response has exactly three full quartet coordinates.')
    if any(type(v) is not int and not isinstance(v, str) for v in values):
        raise ValueError('This executable interface accepts exact rational values only.')
    q = tuple(Fraction(v) for v in values)
    if sum(q) != 1 or any(v <= 0 for v in q):
        raise ValueError('Responses must be positive normalized exact laws.')
    return q

def forced_image(q):
    baseline = min(q)
    targets = [i for i, x in enumerate(q) if x > baseline]
    if len(targets) != 1 or not 0 < 3*baseline < 1:
        raise ValueError('Response is outside every admitted strictly positive forced CF image.')
    a, s = targets[0], 3*baseline
    expected = tuple(1-2*s/3 if i == a else s/3 for i in range(3))
    if q != expected:
        raise ValueError('Forced response has no coherent admitted survival value.')
    return a, s

def execute(request):
    def unknown(reason):
        return {'status':'UNKNOWN_UNSUPPORTED_OR_INCONSISTENT_HISTORY', 'reason':reason,
                'empirical_admission_claimed':False, 'generic_G7_completion_claimed':False}
    try:
        if not isinstance(request, dict) or set(request) - {'observation_kind','n','registry','mechanism','path_budget','history','empirical_admission'}:
            raise ValueError('Unsupported request fields or shape.')
        if not isinstance(request.get('empirical_admission', {}),dict) or request.get('empirical_admission', {}):
            raise ValueError('No empirical admission adapter exists; all nonempty metadata fail closed.')
        if request.get('observation_kind') != 'exact_unranked_law' or request.get('n') != 4:
            raise ValueError('This policy requires exact four-original-tip unranked quartet laws.')
        if request.get('registry') != {'complete':True,'hybrid_ids':['H0']}:
            raise ValueError('This interface requires the complete one-original-hybrid H0 registry.')
        mode = request.get('mechanism')
        if mode not in ('independent','common'):
            raise ValueError('One shared actual mechanism must be specified for all history.')
        budget = request.get('path_budget')
        if not isinstance(budget,list) or len(budget)!=3 or any(type(v) is not int or v<0 for v in budget):
            raise ValueError('PATH budget must contain three nonnegative integers.')
        if any(v < needed for v,needed in zip(budget,[2,2,1])):
            raise ValueError('This selected policy requires PATH budget [2,2,1]; no general losing-budget claim.')
        history = request.get('history',[])
        if not isinstance(history,list) or len(history)>2:
            raise ValueError('The selected policy has at most two response stages.')
        raw = (ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes()
        if hashlib.sha256(raw).hexdigest() != PROVIDER:
            raise ValueError('The accepted complete joint source-image provider changed.')
        provider = json.loads(raw)
        if not history:
            return {'status':'ACTION', 'stage':0, 'programme':[{'weight':'1','forced':{'H0':0}}],
                    'path_budget_required':[2,2,1], 'empirical_admission_claimed':False}
        h = vector(history[0]); a,s = forced_image(h)
        w = h[0]
        action = [{'weight':str(w),'forced':{'H0':0}},
                  {'weight':str(1-w),'forced':{'H0':1}}]
        if len(history)==1:
            return {'status':'ACTION','stage':1,'programme':action,
                    'depends_on_first_response_coordinate':0,'path_cost_after_action':[2,2,1],
                    'empirical_admission_claimed':False}
        z = vector(history[1])
        # Recover the SAME source's second forced law, using the actual earlier
        # response and its response-dependent action. No independent row refit.
        g = tuple((z[i]-w*h[i])/(1-w) for i in range(3))
        b,t = forced_image(g)
        if any(x<=0 for x in g) or sum(g)!=1:
            raise ValueError('The accumulated history has no shared joint source image.')
        selected = [i for i,x in enumerate(z) if x > min(z)]
        if selected != sorted(set((a,b))):
            raise ValueError('The source-certified leaf guard failed.')
        representatives = {tuple(row['forced_rows'][i]['target_coordinate'] for i in (0,1)):row
                           for row in provider['surjection_representatives']}
        import sympy as sp
        source,values = witness(representatives[(a,b)],sp.Rational(s.numerator,s.denominator),sp.Rational(t.numerator,t.denominator))
        coordinates = provider['coordinate_order']
        def law(q): return [{'outcome':coordinates[i],'p':str(p)} for i,p in enumerate(q)]
        actual_request = {'observation_kind':'exact_unranked_law','n':4,
                          'registry':{'complete':True,'hybrid_ids':['H0']},'mechanisms':[mode],
                          'rows':[{'readout':'unrooted_splits','forced':{'H0':0},'law':law(h)},
                                  {'readout':'unrooted_splits','program':action,'law':law(z)}]}
        rows = prepare_request(actual_request)[-1]
        verify_witness(source,mode,rows,values)
        target = target_json(source)['nontrivial_displayed_split_union']
        expected = sorted(tuple(tuple(side) for side in coordinates[i][0]) for i in selected)
        if target != expected:
            raise ValueError('The constructed actual original target failed the leaf.')
        return {'status':'IDENTIFIED_ACTUAL_Q_BY_RESPONSE_DEPENDENT_TWO_STEP_POLICY',
                'path_cost':[2,2,1],'actual_source':graph_json(source),'source_values':values,
                'physical_realization':physical_realization(source,values),
                'shared_history_request':actual_request,'identified_target':target,
                'ordered_forcing_targets':[a,b],'shared_survivals':[str(s),str(t)],
                'verification':'BOTH_ACTUAL_SOURCE_HISTORY_ROWS_RECOMPILED_WITH_ONE_ASSIGNMENT',
                'complete_real_policy_certificate':'ADAPTIVE-POLICY-CERTIFICATE.json',
                'runtime_encoding':'exact rational response vectors',
                'empirical_admission_claimed':False,'generic_G7_completion_claimed':False,
                'optimality_claimed':False,'Lean_certification_claimed':False}
    except (ValueError,TypeError,KeyError,ZeroDivisionError) as error:
        return unknown(str(error))

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('request');p.add_argument('--output',required=True);a=p.parse_args()
    out=execute(json.loads(Path(a.request).read_bytes()))
    Path(a.output).write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'status':out['status'],'path_cost':out.get('path_cost'),'reason':out.get('reason')}))

if __name__=='__main__':main()
