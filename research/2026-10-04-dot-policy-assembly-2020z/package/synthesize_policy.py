"""Connect inherited winning fibres to a whole source-admitted policy.

The policy word is GENERATED, not supplied. Section-candidate exhaustion is
UNKNOWN. This implements one supported provider class, not general G7 CAD.
"""
import hashlib
import json
from pathlib import Path
import sys
import sympy as sp
import z3

ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'projection'))
from compile_projected_word import compile_policy, parsed_action
sys.path.insert(0,str(ROOT/'projection/providers'))
from test_policy_verification import models as admitted_images
from terminal_engine import polynomial_to_z3
sys.path.insert(0,str(ROOT/'terminal-certificate'))
from verify_all_interior_receipt import check as check_positive_pairs

IMAGE_SHA='2332f4a6e242c8a29cf9ce1e39486e4d6ce8a739b4b02d5ce87d85ce69dabcb8'

def provider():
    bindings=json.loads((ROOT/'INHERITED-PROVIDER-BINDINGS.json').read_text())
    for row in bindings['files']:
        raw=(ROOT/row['path']).read_bytes()
        if len(raw)!=row['bytes'] or hashlib.sha256(raw).hexdigest()!=row['sha256']:
            raise ValueError('An accepted provider byte changed.')
    raw=(ROOT/'projection/providers/FORCED-PAIR-SOURCE-IMAGE-CERTIFICATE.json').read_bytes()
    if hashlib.sha256(raw).hexdigest()!=IMAGE_SHA:
        raise ValueError('The complete original source image changed.')
    proof=check_positive_pairs(json.loads((ROOT/'terminal-certificate/ALL-INTERIOR-EXPERIMENT-RECEIPT.json').read_text()))
    sources=admitted_images()
    # Forcing both original bits hides, but does not refit, natural gamma.
    for source in sources:source['variables'] += [sp.Symbol('originalProtectedNaturalGammaH0')]
    return sources,proof

def certify_observation_section(models, first_row, expression, milliseconds=3000):
    """ONE section must lie in the chosen full-support winning region for ALL sources.

    Rival pairs used separate assignments in the inherited positive proof.
    Here each candidate retains its own one original map through its first law.
    """
    histories=[sp.Dummy(f'controllerHistory0_{j}') for j in range(3)]
    value,domains=parsed_action(expression,{f'h0_{j}':h for j,h in enumerate(histories)})
    receipts=[]
    for owner,model in enumerate(models):
        observed=dict(zip(histories,model['laws'][first_row]))
        forward=sp.cancel(value.xreplace(observed))
        point={v:z3.FreshReal('oneOriginalSectionSource') for v in model['variables']}
        domain=z3.And(*[z3.And(v>0,v<1) for v in point.values()])
        num,den=sp.fraction(forward)
        defined=[]
        for written in domains:
            n,d=sp.fraction(sp.cancel(written.xreplace(observed)))
            defined.extend([polynomial_to_z3(n,point)!=0,polynomial_to_z3(d,point)!=0])
        nz=polynomial_to_z3(num,point);dz=polynomial_to_z3(den,point)
        legal=z3.And(dz!=0,nz*dz>0,(dz-nz)*dz>0,*defined)
        solver=z3.SolverFor('QF_NRA');solver.set(timeout=milliseconds)
        solver.add(domain,z3.Not(legal));result=solver.check()
        receipts.append({'source_model':owner,'status':str(result),'query_smt2':solver.to_smt2()})
        if result!=z3.unsat:
            return {'status':'UNKNOWN_OR_REFUTED_SECTION','receipts':receipts}
    return {'status':'SECTION_IN_CERTIFIED_FULL_SUPPORT_WINNING_REGION_FOR_ALL_SOURCE_HISTORIES_SAME_BACKEND',
            'expression':expression,'receipts':receipts,'certified_full_support_winning_region':'0<weight<1',
            'chosen_support':[0,1],'whole_menu_winning_fibre_claimed':False,
            'source_history_assignment_shared':True,'section_reads_only_prior_response':True}

def synthesize(request):
    attempts=[]
    try:
        if not isinstance(request,dict) or set(request)!={'source_provider','mechanism','budget','prefer_adaptive'}:
            raise ValueError('This supported source-provider synthesis request has exact declared fields.')
        if request['source_provider']!='complete_n4_r1_two_original_forcings':
            raise ValueError('No synthesis admission for another source/provider class.')
        if request['mechanism'] not in ('common','independent'):
            raise ValueError('One actual mechanism must be fixed through all calls.')
        budget=request['budget']
        if not isinstance(budget,list) or len(budget)!=3 or any(type(x) is not int or x<0 for x in budget):
            raise ValueError('Malformed PATH budget.')
        if request['prefer_adaptive'] is not True:
            raise ValueError('This milestone constructs an adaptive witness, not a Pareto optimizer.')
        if any(x<needed for x,needed in zip(budget,[2,2,1])):
            raise ValueError('No affordable witness in this adaptive construction; no losing-budget claim.')
        models,proof=provider()
        # First eligible cheap forcing support. No prerequisite actuation is
        # added: this is a chosen witness in the original deletion-closed menu.
        for first_row in (0,1):
            first_weights=['1','0'] if first_row==0 else ['0','1']
            for candidate in [f'h0_{j}' for j in range(3)]+['1/2']:
                section=certify_observation_section(models,first_row,candidate)
                attempts.append({'first_original_forcing':first_row,'section_candidate':candidate,'check':section})
                if section['status']!='SECTION_IN_CERTIFIED_FULL_SUPPORT_WINNING_REGION_FOR_ALL_SOURCE_HISTORIES_SAME_BACKEND':
                    continue
                generated_calls=[{'support':[first_row],'weights':first_weights},
                                 {'support':[0,1],'weights':[candidate,'1-('+candidate+')']}]
                compiled=compile_policy(models,generated_calls,[[0],[1],[0,1]],[['H0'],['H0']],budget)
                if compiled['status']!='WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND':
                    attempts.append({'candidate_decoder_status':compiled['status']})
                    continue
                return {'status':'AUTOMATIC_SOURCE_ADMITTED_ADAPTIVE_POLICY_SYNTHESIZED_AND_VERIFIED_SAME_BACKEND',
                        'request':request,'policy':compiled['policy'],'generated_calls':generated_calls,
                        'source_projection_and_whole_policy_certificate':compiled,'section_attempts':attempts,
                        'inherited_different_target_pair_certificate':proof,
                        'winning_relation':'certified chosen full-support positive two-row region; broader history-conditioned menu can include endpoints',
                        'quantifier_order':'exists first legal action; for every source-generated first response, choose one observation-only certified section; for every next response, output the unique source-consistent target',
                        'candidate_sources_share_one_assignment_across_all_history':True,
                        'two_rivals_have_separate_assignments':True,
                        'complete_reachable_response_coverage':True,
                        'policy_word_was_supplied_by_caller':False,
                        'finite_section_search_complete_for_general_G7':False,
                        'optimality_claimed':False,'earlier_one_call_fixture_optimum_preserved':True,
                        'new_source_census_or_G3_G4_Lean_empirical_claimed':False}
        return {'status':'UNKNOWN_NO_CERTIFIED_SECTION_OR_DECODER_EXTRACTED','attempts':attempts,
                'mathematical_budget_NO_claimed':False}
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,SyntaxError,ArithmeticError,RecursionError,
            sp.PolynomialError,z3.Z3Exception) as error:
        return {'status':'UNKNOWN_UNSUPPORTED_OR_RESOURCE_LIMIT','reason':str(error),
                'attempts':attempts,'mathematical_budget_NO_claimed':False}

if __name__=='__main__':
    request={'source_provider':'complete_n4_r1_two_original_forcings','mechanism':'common',
             'budget':[2,2,1],'prefer_adaptive':True}
    result=synthesize(request)
    (ROOT/'SYNTHESIS-RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    if result['status'].startswith('AUTOMATIC_'):
        (ROOT/'GENERATED-ADAPTIVE-POLICY.json').write_text(json.dumps(result['policy'],indent=2)+'\n')
    print(json.dumps({'status':result['status'],'generated_calls':result.get('generated_calls'),
                      'word_supplied_by_caller':False,'generic_G7_completion':False},indent=2))
