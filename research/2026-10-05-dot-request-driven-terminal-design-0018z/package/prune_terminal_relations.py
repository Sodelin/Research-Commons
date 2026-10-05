"""Proof-recorded exact pruning of GLOBAL empty projected cells.

Every dropped formula has an exact QF_NRA UNSAT receipt. SAT or UNKNOWN cells
are preserved unchanged, so no sampled or unproved simplification is used.
This changes the backend presentation, not source or quantifier semantics.
"""
import copy,ctypes,json
from pathlib import Path
import z3
from verify_algebraic_policy import guard

def _prune(prepared,milliseconds=3000,max_queries=512):
    if prepared.get('status')!='COMPLETE_DECLARED_AFFINE_TERMINAL_MENU_RELATIONS':
        return {'status':'UNKNOWN_INCOMPLETE_TERMINAL_RELATIONS','global_budget_NO_claimed':False}
    if type(milliseconds) is not int or not 0<milliseconds<=60000 or type(max_queries) is not int or max_queries<1:
        return {'status':'UNKNOWN_INVALID_PRUNING_LIMIT','global_budget_NO_claimed':False}
    result=copy.deepcopy(prepared);receipts=[];cache={}
    for entry in result['relations']:
        fibre=entry['fibre'];known=fibre['history_coordinates']+fibre['free_action_coordinates']
        scope={name:z3.FreshReal('retainedTerminalIdentity') for name in known}
        _,all_defined=guard(fibre['winning_relation'],scope)
        if not z3.is_true(z3.simplify(all_defined)):
            raise ValueError('Pruning requires total polynomial projected guards; written nonconstant division is unsupported here.')
        def empty(node,label):
            key=json.dumps([known,node],sort_keys=True,separators=(',',':'))
            if key in cache:return cache[key]
            if len(receipts)>=max_queries:return False
            formula,defined=guard(node,scope)
            solver=z3.SolverFor('QF_NRA');solver.set(timeout=milliseconds);solver.add(z3.And(defined,formula))
            status=solver.check();receipt={'menu_index':entry['menu_index'],'label':label,'status':str(status),'query_smt2':solver.to_smt2()}
            if status==z3.unknown:receipt['reason']=solver.reason_unknown()
            receipts.append(receipt);cache[key]=status==z3.unsat
            return cache[key]
        def visit(node,label):
            if type(node) is bool:return node
            op=node['op']
            if op=='and':
                children=[visit(x,label+['and',i]) for i,x in enumerate(node['args'])]
                if any(x is False for x in children):return False
                children=[x for x in children if x is not True]
                if not children:return True
                answer={'op':'and','args':children}
                return False if empty(answer,label) else answer
            if op=='or':
                children=[visit(x,label+['or',i]) for i,x in enumerate(node['args'])]
                if any(x is True for x in children):return True
                unique={json.dumps(x,sort_keys=True,separators=(',',':')):x for x in children if x is not False}
                children=[unique[k] for k in sorted(unique)]
                return {'op':'or','args':children} if children else False
            if op=='not':
                child=visit(node['arg'],label+['not'])
                return not child if type(child) is bool else {'op':'not','arg':child}
            return node
        reduced=visit(fibre['winning_relation'],['winning'])
        if reduced is not False and empty(reduced,['whole_winning']):reduced=False
        fibre['winning_relation']=reduced
        fibre['presentation_pruning_only']=True
    return {'status':'COMPLETE_TERMINAL_RELATIONS_WITH_CHECKED_EMPTY_CELL_PRUNING','prepared':result,
            'pruning_receipts':receipts,'UNKNOWN_cells_preserved':True,'symbolic_trust':'SAME_BACKEND_Z3',
            'source_equations_parameter_ties_and_quantifier_order_unchanged':True,'global_budget_NO_claimed':False}

def prune(prepared,milliseconds=3000,max_queries=512):
    try:return _prune(prepared,milliseconds,max_queries)
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,SyntaxError,ArithmeticError,RecursionError,MemoryError,ctypes.ArgumentError,z3.Z3Exception) as error:
        return {'status':'UNKNOWN_TERMINAL_RELATION_PRUNING','reason':str(error),'global_budget_NO_claimed':False}

def run():
    root=Path(__file__).resolve().parent
    out=prune(json.loads((root/'PREPARED-TERMINAL-REQUEST.json').read_text()))
    (root/'PRUNED-TERMINAL-REQUEST.json').write_text(json.dumps(out,indent=2)+'\n')
    assert out['status']=='COMPLETE_TERMINAL_RELATIONS_WITH_CHECKED_EMPTY_CELL_PRUNING'
    from prepare_terminal_request import wolfram_query
    combined=(root/'actual-affine-terminal-cad-selector-principal-root.wl').read_text()
    export=combined[combined.index('(* Exact AST export'):combined.rindex('Module[{relation,result,export}')]
    query=wolfram_query(out['prepared'],(root/'cad_selector_principal_root.wl').read_text(),export)
    (root/'GENERATED-PRUNED-REQUEST-TERMINAL-SELECTOR.wl').write_text(query)
    print(json.dumps({'status':out['status'],'exact_global_queries':len(out['pruning_receipts']),
                     'query_bytes':len(query.encode()),'winning_relation_bytes':[len(json.dumps(e['fibre']['winning_relation'])) for e in out['prepared']['relations']]}))
if __name__=='__main__':run()
