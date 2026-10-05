"""Bind one complete terminal CAD selector to an admitted whole source policy.

The past action word is supplied. Affine terminal projection, complete CAD
coverage and target projection have distinct evidence. Unsupported Root guard
inlining and nonconstant action ASTs remain UNKNOWN in this serializer.
"""
import copy,json
from pathlib import Path
import z3
from compile_projected_word import compile_policy
from cad_value import evaluate_value
from verify_policy import verify

def rational_text(node):
    if not isinstance(node,dict):raise ValueError('Malformed exact selector value.')
    kind=node.get('kind')
    if kind=='rational' and set(node)=={'kind','value'}:
        # Validate rather than copying arbitrary text into the policy parser.
        out,v=evaluate_value(node,{})
        if out['status']!='EXACT_STRUCTURED_CAD_VALUE_SAME_BACKEND' or not z3.is_rational_value(v):raise ValueError('Malformed rational selector value.')
        return str(v.as_fraction())
    if kind=='observation' and set(node)=={'kind','name'}:
        name=node['name']
        if not isinstance(name,str) or not name.startswith('h') or not name.isidentifier():raise ValueError('Unsupported observation identity.')
        return name
    if kind in ('add','multiply') and set(node)=={'kind','args'} and isinstance(node['args'],list) and node['args']:
        return '('+('+' if kind=='add' else '*').join(rational_text(v) for v in node['args'])+')'
    if kind=='power' and set(node)=={'kind','base','exponent'} and type(node['exponent']) is int and node['exponent']>=0:
        return '('+rational_text(node['base'])+')**'+str(node['exponent'])
    if kind=='divide' and set(node)=={'kind','numerator','denominator'}:
        return '('+rational_text(node['numerator'])+')/('+rational_text(node['denominator'])+')'
    raise ValueError('This whole-policy serializer cannot inline general Root/min/max guard or action expressions yet.')

def legacy_guard(tree,depth=0):
    if depth>64:raise ValueError('Guard export resource ceiling exceeded.')
    if not isinstance(tree,dict):raise ValueError('Malformed exact selector guard.')
    kind=tree.get('kind')
    if kind=='boolean' and set(tree)=={'kind','value'} and type(tree['value']) is bool:return tree['value']
    if kind in ('and','or') and set(tree)=={'kind','args'} and isinstance(tree['args'],list):return {'op':kind,'args':[legacy_guard(v,depth+1) for v in tree['args']]}
    if kind=='not' and set(tree)=={'kind','arg'}:return {'op':'not','arg':legacy_guard(tree['arg'],depth+1)}
    if kind=='comparison' and set(tree)=={'kind','op','left','right'} and tree['op'] in ('eq','ne','lt','le','gt','ge'):
        return {'op':tree['op'],'left':rational_text(tree['left']),'right':rational_text(tree['right'])}
    raise ValueError('Unsupported exact selector guard shape.')

def assemble(models,prefix,selector,support,supports,row_sites,budget):
    try:
        if selector.get('SelectorStatus')!='SEMIALGEBRAIC_FIBRE_SELECTOR_CERTIFIED_SAME_BACKEND':raise ValueError('No complete backend selector.')
        exported=selector['Export']
        if exported['Status']!='CERTIFIED_HISTORY_FIRST_SELECTOR_AST_EXPORTED_SAME_BACKEND' or exported['coverage'] is not True or not all(v is True for v in exported['soundness']):raise ValueError('Selector coverage/soundness is incomplete.')
        cells=exported['cells']
        if not isinstance(cells,list) or not cells:raise ValueError('No reachable selector cell.')
        branches=[];decoder_receipts=[];decoder_cache={};cell_decoder_indices=[]
        for cell in cells:
            if not isinstance(cell,dict) or set(cell)!={'guard','weights'}:raise ValueError('Malformed selector cell.')
            texts=[rational_text(v) for v in cell['weights']]
            # This first integrated path keeps terminal weights CONSTANT so the
            # accepted affine word projection derives exact target leaves for
            # the complete source history. No action candidate library is used.
            for text in texts:
                out,v=evaluate_value({'kind':'rational','value':text},{})
                if out['status']!='EXACT_STRUCTURED_CAD_VALUE_SAME_BACKEND':raise ValueError('Nonconstant CAD actions need the next serializer gate.')
            call={'support':support,'weights':texts}
            key=tuple(texts)
            if key in decoder_cache:
                index=decoder_cache[key];decoded=decoder_receipts[index]
            else:
                decoded=compile_policy(models,prefix+[call],supports,row_sites,budget,seconds=30)
                if decoded['status']!='WHOLE_ACTION_WORD_PROJECTED_AND_VERIFIED_SAME_BACKEND':raise ValueError('Complete target projection or whole-word verification remained UNKNOWN.')
                index=len(decoder_receipts);decoder_cache[key]=index;decoder_receipts.append(decoded)
            node=decoded['policy']
            for _ in range(len(prefix)):node=node['next']
            branches.append({'guard':legacy_guard(cell['guard']),'next':node})
            cell_decoder_indices.append(index)
        policy={'kind':'decision','branches':branches}
        for call in reversed(prefix):policy={**copy.deepcopy(call),'kind':'call','next':policy}
        checked=verify(models,policy,supports,row_sites,budget,milliseconds=5000)
        if checked['status']!='FIXED_ADAPTIVE_POLICY_VERIFIED_SAME_BACKEND':raise ValueError('Final entire source-policy gate failed or remained UNKNOWN.')
        return {'status':'COMPLETE_TERMINAL_CAD_SELECTOR_ASSEMBLED_AND_WHOLE_POLICY_VERIFIED_SAME_BACKEND','policy':policy,'verification':checked,'decoder_receipts':decoder_receipts,'cell_decoder_indices':cell_decoder_indices,
                'source_shared_through_all_histories':True,'first_eligible_CAD_cell_order_retained':True,'action_library_search_used':False,
                'supplied_prefix':prefix,'whole_policy_budget':budget,'generic_deeper_recursive_synthesis_claimed':False,
                'limits':'One supplied-prefix terminal selector; this serializer currently requires constant rational returned actions and arithmetic guards'}
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,SyntaxError,ArithmeticError,RecursionError,z3.Z3Exception) as error:
        return {'status':'UNKNOWN_CAD_WHOLE_POLICY_ASSEMBLY','reason':str(error),'global_budget_NO_claimed':False}

def run():
    from provider_models import models
    root=Path(__file__).resolve().parent
    selector=json.loads((root/'EXPORTED-ACTUAL-TERMINAL-SELECTOR.json').read_text())
    result=assemble(models(),[{'support':[0],'weights':['1','0']}],selector,[0,1],[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
    (root/'CAD-ASSEMBLED-POLICY-RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    assert result['status']=='COMPLETE_TERMINAL_CAD_SELECTOR_ASSEMBLED_AND_WHOLE_POLICY_VERIFIED_SAME_BACKEND',{'status':result['status'],'reason':result.get('reason')}
    (root/'CAD-ASSEMBLED-POLICY.json').write_text(json.dumps(result['policy'],indent=2)+'\n')
    print(json.dumps({'status':result['status'],'CAD_cells':len(selector['Export']['cells']),'final_obligations':len(result['verification']['receipts']),'generic_deeper_synthesis_claimed':False}))
if __name__=='__main__':run()
