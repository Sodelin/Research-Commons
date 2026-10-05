"""Complete declared-menu terminal CAD -> one verified whole source policy.

No selector/action/support is supplied by the caller. The prefix remains input.
The producer projects every afforded configured support. Complete CAD selects
among those winning choices; the final policy gate verifies actual source rows.
This does not extract the deeper recursive G7 strategy or prove an optimum.
"""
import copy,json
from fractions import Fraction
from pathlib import Path
import z3
from assemble_cad_terminal_policy import legacy_guard
from project_branch_word import project_branch_word
from cad_action_sections import ActionSectionWriter
from verify_algebraic_policy import verify

def assemble(models,prepared,selector):
    checked=None
    try:
        if prepared.get('status')!='COMPLETE_DECLARED_AFFINE_TERMINAL_MENU_RELATIONS':raise ValueError('Incomplete menu/source projection.')
        if selector.get('SelectorStatus')!='SEMIALGEBRAIC_FIBRE_SELECTOR_CERTIFIED_SAME_BACKEND':raise ValueError('No complete certified history-first CAD.')
        exported=selector['Export'];cells=exported['cells']
        if (exported.get('Status')!='CERTIFIED_HISTORY_FIRST_SELECTOR_AST_EXPORTED_SAME_BACKEND'
                or exported.get('coverage') is not True or not isinstance(exported.get('soundness'),list)
                or len(exported['soundness'])!=len(cells) or not all(v is True for v in exported['soundness'])):
            raise ValueError('Incomplete CAD coverage/soundness.')
        k,q=prepared['source_dimensions'];prefix=prepared['supplied_prefix'];menu=prepared['configured_supports']
        if not isinstance(cells,list) or not cells:raise ValueError('No complete selector cells.')
        branches=[];decoder_receipts=[];cache={};operational=[];discarded=[]
        for original_index,cell in enumerate(cells):
            if not isinstance(cell,dict) or set(cell)!={'guard','weights'} or not isinstance(cell['weights'],list) or len(cell['weights'])!=k+1:
                raise ValueError('Tagged selector cannot truncate original action/menu coordinates.')
            menu_ast=cell['weights'][-1]
            if not isinstance(menu_ast,dict) or set(menu_ast)!={'kind','value'} or menu_ast['kind']!='rational' or not isinstance(menu_ast['value'],str):
                raise ValueError('A configured menu choice must be an exact constant integer, not an inferred algebraic tag.')
            tag=Fraction(menu_ast['value'])
            if tag.denominator!=1 or not 0<=tag.numerator<len(menu):raise ValueError('Configured menu index is out of range.')
            selected=menu[tag.numerator];history_guard=legacy_guard(cell['guard'])
            # This is only syntactic False, never a sampled unreachable cell.
            if history_guard is False:discarded.append(original_index);continue
            call=ActionSectionWriter(len(prefix)).call(cell['weights'][:-1],selected)
            key=json.dumps(call,sort_keys=True,separators=(',',':'))
            if key not in cache:
                decoded=project_branch_word(models,prefix+[call],menu,prepared['row_sites'],prepared['budget'],seconds=30)
                if decoded['status']!='COMPLETE_AFFINE_LEGAL_WORD_TARGET_REGIONS_PROJECTED':raise ValueError('Complete conditional source target projection remained UNKNOWN.')
                cache[key]=len(decoder_receipts);decoder_receipts.append(decoded)
            decoded=decoder_receipts[cache[key]];node=decoded['policy_candidate']
            for _ in prefix:node=node['next']
            branches.append({'guard':history_guard,'next':node})
            operational.append({'guard':cell['guard'],'weights':cell['weights'][:-1]})
        if not branches:raise ValueError('No nonempty source history branch remains.')
        policy={'kind':'decision','branches':branches}
        for call in reversed(prefix):policy={**copy.deepcopy(call),'kind':'call','next':policy}
        checked=verify(models,policy,menu,prepared['row_sites'],prepared['budget'],milliseconds=5000)
        if checked['status']!='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND':raise ValueError('Final whole source-policy verification failed or remained UNKNOWN.')
        return {'status':'REQUEST_DRIVEN_TERMINAL_POLICY_VERIFIED_SAME_BACKEND','policy':policy,'verification':checked,
                'decoder_receipts':decoder_receipts,'discarded_syntactic_false_cell_indices':discarded,
                'complete_backend_cells':len(cells),'selected_policy_cells':len(branches),
                'operational_selector':{'Export':{'cells':operational}},'one_source_per_candidate_through_entire_history':True,
                'support_and_action_selected_from_complete_declared_menu_fibres':True,'menu_priority':'larger affordable supports first, then declared menu order; a tie breaker, no optimality claim',
                'no_action_library_used':True,'caller_supplied_selector_or_terminal_support':False,
                'exactly_one_further_call_attempted':True,'generic_recursive_synthesis_claimed':False,'global_budget_NO_claimed':False}
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,SyntaxError,ArithmeticError,RecursionError,MemoryError,z3.Z3Exception) as error:
        return {'status':'UNKNOWN_REQUEST_POLICY_ASSEMBLY','reason':str(error),'whole_policy_attempt':checked,'global_budget_NO_claimed':False}

def run():
    from provider_models import models
    root=Path(__file__).resolve().parent
    prepared=json.loads((root/'PRUNED-TERMINAL-REQUEST.json').read_text())['prepared']
    selector=json.loads((root/'EXPORTED-REQUEST-TERMINAL-SELECTOR.json').read_text())
    result=assemble(models(),prepared,selector)
    (root/'REQUEST-POLICY-RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    assert result['status']=='REQUEST_DRIVEN_TERMINAL_POLICY_VERIFIED_SAME_BACKEND',result.get('reason')
    (root/'CAD-ASSEMBLED-POLICY.json').write_text(json.dumps(result['policy'],indent=2)+'\n')
    (root/'OPERATIONAL-SELECTOR.json').write_text(json.dumps(result['operational_selector'],indent=2)+'\n')
    print(json.dumps({'status':result['status'],'backend_cells':result['complete_backend_cells'],'selected_policy_cells':result['selected_policy_cells'],'whole_policy_obligations':len(result['verification']['receipts'])}))
if __name__=='__main__':run()
