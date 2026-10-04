#!/usr/bin/env python3
"""Source-backed policy and lower witnesses for the two original forcing rows."""
from pathlib import Path
import json
import hashlib
import sys
import sympy as sp
from sympy.printing.mathematica import mathematica_code
ROOT = Path(__file__).resolve().parent
BASE = ROOT/'sourcekit'
sys.path.insert(0, str(BASE))
from solver import (Network, admitted, prepare_request, verify_witness, physical_realization,
                    unrooted_law, compile_law, displayed, target_json, graph_json)


def root_encoding(q, degree):
    if degree == 1:
        return {'kind': 'rational', 'value': str(q)}
    return {'kind': 'algebraic', 'polynomial_ascending': [str(-q)]+['0']*(degree-1)+['1'],
            'real_root_index': 2 if degree % 2 == 0 else 1}


def witness(row, s, t):
    g = row['graph'];source = Network(tuple(tuple(e) for e in g['edges']),g['root'],tuple(g['leaves']))
    if not admitted(source) or set(source.leaves)!={f'L{i}' for i in range(4)} or set(source.structure()[3])!={'H0'}:
        raise RuntimeError('Surjection representative is outside the declared actual n4/r1 source class.')
    values = {str(v): {'kind': 'rational', 'value': '1/2'} for v in list(source.parameters()[0])+list(source.parameters()[1].values())}
    common, left, right = row['shared'], row['exclusive0'], row['exclusive1']
    c = (1+max(s,t))/2 if common else sp.Rational(1)
    for names, value in ((common,c),(left,s/c),(right,t/c)):
        for name in names:values[name] = root_encoding(value,len(names))
    return source, values


def main():
    certificate = json.loads((ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes())
    if certificate['source_count'] != 546 or certificate['source_image_model_count'] != 9:
        raise RuntimeError('Incomplete actual source image certificate.')
    s,t,w = sp.symbols('s t w')
    checks = []
    wolfram_conditions = []
    representatives = {tuple(row['forced_rows'][i]['target_coordinate'] for i in (0,1)):row
                       for row in certificate['surjection_representatives']}
    for a in range(3):
        for b in range(3):
            baseline = (w*s+(1-w)*t)/3
            law = [sp.expand(baseline+w*(1-s)*int(i==a)+(1-w)*(1-t)*int(i==b)) for i in range(3)]
            if sp.expand(sum(law)-1) != 0:
                raise RuntimeError('Pooled source law is not normalized.')
            absent = next(i for i in range(3) if i not in (a,b))
            if sp.expand(law[absent]-baseline) != 0:
                raise RuntimeError('Missing baseline coordinate.')
            expected = [sp.expand(w*(1-s)*int(i==a)+(1-w)*(1-t)*int(i==b)) for i in range(3)]
            if any(sp.expand(law[i]-baseline-expected[i]) != 0 for i in range(3)):
                raise RuntimeError('Target excess identity failure.')
            conditions = []
            for i in range(3):
                relation = f'({mathematica_code(law[i]-baseline)})' + ('>0' if i in (a,b) else '==0')
                conditions.append(relation)
            wolfram_conditions.append('ForAll[{s,t,w},0<s<1 && 0<t<1 && 0<w<1,'+' && '.join(conditions)+']')
            checks.append({'ordered_pair':[a,b],'pooled_law':[str(v) for v in law],
                           'absent_coordinate':absent,'target_excess_identities':[str(v) for v in expected],
                           'status':'EXACT_POLYNOMIAL_IDENTITIES_CHECKED'})

    lower = []
    # Each single chosen original forcing bit admits different complete-Q targets
    # with exactly the SAME positive response. Extra repeated calls cannot help.
    for bit in (0,1):
        pair1=(0,0);pair2=(0,1) if bit==0 else (1,0)
        witnesses=[]
        observed=None
        for pair in (pair1,pair2):
            source, values = witness(representatives[pair],sp.Rational(1,2),sp.Rational(1,2))
            coordinates=certificate['coordinate_order'];law=[sp.Rational(2,3) if i==0 else sp.Rational(1,6) for i in range(3)]
            request={'observation_kind':'exact_unranked_law','n':4,
                     'registry':{'complete':True,'hybrid_ids':['H0']},'mechanisms':['independent'],
                     'rows':[{'forced':{'H0':bit},'readout':'unrooted_splits',
                              'law':[{'outcome':coordinates[i],'p':str(p)} for i,p in enumerate(law)]}]}
            rows=prepare_request(request)[-1]
            verify_witness(source,'independent',rows,values)
            witnesses.append({'source':graph_json(source),'values':values,
                              'actual_target':target_json(source)['nontrivial_displayed_split_union'],
                              'physical_realization':physical_realization(source,values),
                              'joint_response_request':request})
        if witnesses[0]['actual_target'] == witnesses[1]['actual_target']:
            raise RuntimeError('Lower witnesses do not have different actual targets.')
        lower.append({'chosen_original_bit':bit,'same_exact_response':[str(v) for v in law],
                      'witnesses':witnesses,'status':'PASS_INDEPENDENT_ACTUAL_SOURCE_WITNESS_RECOMPILATION'})
    report={'schema':'actual-complete-n4-r1-forced-pair-policy-and-lower-bound-v1',
            'source_image_certificate_sha256':hashlib.sha256((ROOT/'FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes()).hexdigest(),
            'scope':'Complete546 original n4/r1 admitted sources; menu ONLY original forcing0/1; unlabelled positive pooled one-copy quartet law; free edge-specific clocks.',
            'source_checks':checks,'single_configuration_lower_witnesses':lower,
            'source_valid_policy':'For any strictly positive weights on BOTH rows, return exactly the coordinates strictly above the minimum pooled concordance factor.',
            'matched_trajectory_cost':{'exact_calls':1,'configurations':2,'original_controlled_sites':1},
            'generic_CAD_extraction_or_unbounded_source_master_claimed':False,
            'Lean_verification_claimed':False}
    (ROOT/'FORCED-PAIR-POLICY-CERTIFICATE.json').write_text(json.dumps(report,indent=2)+'\n')
    query='<|"ActualOriginalSourceCount"->546,"AllNineSourceImagePolicyChecks"->Resolve['+' && '.join(wolfram_conditions)+',Reals],"StrictInteriorWeightExample"->FindInstance[0<a<1 && 0<b<1 && a+b==1,{a,b},Reals,1]|>'
    (ROOT/'forced_pair_policy_checks.wl').write_text(query+'\n')
    print(json.dumps({'status':'PASS_ACTUAL_SOURCE_POLICY_IDENTITIES_AND_LOWER_WITNESSES',
                      'source_images':9,'single_configuration_lower_cases':2,
                      'policy_certificate_sha256':hashlib.sha256((ROOT/'FORCED-PAIR-POLICY-CERTIFICATE.json').read_bytes()).hexdigest()},indent=2))


if __name__=='__main__':main()
