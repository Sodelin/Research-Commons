"""Finite affine terminal request -> complete declared-menu winning relations.

The method is the accepted last-call rival-pair reduction, with one persistent
source assignment per rival through its entire history. This attempts exactly
one further call. A supplied budget may permit more; failure here is UNKNOWN
for general deeper synthesis. Original source-provider admission is separate.
"""
import ast,ctypes,json,time
import sympy as sp
import z3
from pathlib import Path
from terminal_engine import validate_models
from terminal_fibres import compile_terminal_fibre

class RequestLimit(ValueError):pass

def prepare(models,prefix,supports,row_sites,budget,seconds=60):
    completed=[];unaffordable=[]
    try:
        if type(seconds) is not int or not 1<=seconds<=300:raise RequestLimit('Invalid bounded terminal request runtime.')
        if not isinstance(models,list) or not models:raise ValueError('Nonempty finite source model carrier required.')
        k,q=validate_models(models)
        if (not isinstance(supports,list) or not supports or len(supports)>32
                or any(not isinstance(s,list) or not s or any(type(i) is not int or not 0<=i<k for i in s)
                       or len(set(s))!=len(s) for s in supports)):
            raise ValueError('Unsupported configured support menu.')
        if len({tuple(sorted(s)) for s in supports})!=len(supports):raise ValueError('Configured support menu has duplicate supports.')
        if not isinstance(prefix,list) or len(prefix)>120:raise ValueError('Unsupported finite historical call word.')
        allowed={tuple(sorted(s)) for s in supports}
        for call in prefix:
            if (not isinstance(call,dict) or set(call)!={'support','weights'}
                    or not isinstance(call['support'],list) or not call['support']
                    or any(type(i) is not int or not 0<=i<k for i in call['support'])
                    or len(set(call['support']))!=len(call['support'])
                    or tuple(sorted(call['support'])) not in allowed):
                raise ValueError('Historical support is malformed or outside the configured menu.')
        if (not isinstance(row_sites,list) or len(row_sites)!=k or any(not isinstance(s,(list,tuple,set))
                or any(not isinstance(site,str) for site in s) for s in row_sites)):
            raise ValueError('Declared original row-site carrier mismatch.')
        if not isinstance(budget,list) or len(budget)!=3 or any(type(v) is not int or v<0 for v in budget):raise ValueError('Invalid declared PATH budget.')
        start=time.monotonic()
        for index,support in enumerate(supports):
            remaining=int(seconds-(time.monotonic()-start))
            if remaining<1:raise RequestLimit('Complete menu projection exceeded runtime; UNKNOWN.')
            fibre=compile_terminal_fibre(models,prefix,support,row_sites,budget,seconds=min(15,remaining),max_branches=256,max_pairs=2000)
            if fibre['status']=='PROPOSED_SUPPORT_NOT_PATH_AFFORDABLE':
                unaffordable.append({'menu_index':index,'support':support,'path_cost':fibre['path_cost']});continue
            if fibre['status']!='TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED':
                raise RequestLimit('A required menu fibre remained incomplete: '+fibre.get('reason',fibre['status']))
            completed.append({'menu_index':index,'support':support,'fibre':fibre})
        if not completed:raise RequestLimit('No one-further-call support is PATH affordable; deeper/zero-call inference is not attempted.')
        return {'status':'COMPLETE_DECLARED_AFFINE_TERMINAL_MENU_RELATIONS','relations':completed,'unaffordable_supports':unaffordable,
                'configured_supports':supports,'source_dimensions':[k,q],'supplied_prefix':prefix,'row_sites':row_sites,'budget':budget,
                'one_source_per_rival_through_all_rows':True,'exactly_one_further_call_attempted':True,
                'general_recursive_synthesis_claimed':False,'global_budget_NO_claimed':False,
                'source_provider_admission':'conditional on separately pinned complete finite source-model contract'}
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,SyntaxError,ArithmeticError,RecursionError,MemoryError,ctypes.ArgumentError,sp.PolynomialError,z3.Z3Exception) as error:
        return {'status':'UNKNOWN_TERMINAL_REQUEST_PREPARATION','reason':str(error),'completed_relations':completed,
                'unaffordable_supports':unaffordable,'global_budget_NO_claimed':False}

def wolfram_query(prepared,selector_source,export_source,seconds=12):
    """Capture-avoiding export from exact projected AST; no raw source text."""
    if prepared.get('status')!='COMPLETE_DECLARED_AFFINE_TERMINAL_MENU_RELATIONS':raise ValueError('No complete configured-menu projection.')
    k,q=prepared['source_dimensions'];prefix=prepared['supplied_prefix']
    history=[f'h{s}_{j}' for s in range(len(prefix)) for j in range(q)]
    history_ids={name:f'g7TypedHistory{i}' for i,name in enumerate(history)}
    weight_ids=[f'g7TypedWeight{i}' for i in range(k-1)]
    weight_expr=weight_ids+['(1-'+('+'.join(weight_ids) if weight_ids else '0')+')']
    tag='g7TypedMenuIndex';parts=[]
    def arith(text,names):
        def go(node,depth=0):
            if depth>64:raise RequestLimit('Projected expression export resource ceiling.')
            if isinstance(node,ast.Constant) and type(node.value) is int:return str(node.value)
            if isinstance(node,ast.Name) and node.id in names:return names[node.id]
            if isinstance(node,ast.UnaryOp) and isinstance(node.op,ast.USub):return '-('+go(node.operand,depth+1)+')'
            if isinstance(node,ast.BinOp):
                a=go(node.left,depth+1);b=go(node.right,depth+1)
                operations={ast.Add:'+',ast.Sub:'-',ast.Mult:'*',ast.Div:'/',ast.Pow:'^'}
                if type(node.op) in operations:return '('+a+operations[type(node.op)]+b+')'
            raise ValueError('Undeclared identity or unsupported exact projected arithmetic.')
        return go(ast.parse(text,mode='eval').body)
    def guard(node,names):
        if type(node) is bool:return 'True' if node else 'False'
        op=node['op']
        if op in ('and','or'):return ('And' if op=='and' else 'Or')+'['+','.join(guard(x,names) for x in node['args'])+']'
        if op=='not':return 'Not['+guard(node['arg'],names)+']'
        heads={'eq':'Equal','ne':'Unequal','lt':'Less','le':'LessEqual','gt':'Greater','ge':'GreaterEqual'}
        if op not in heads:raise ValueError('Unsupported relation operator.')
        return heads[op]+'['+arith(node['left'],names)+','+arith(node['right'],names)+']'
    for entry in prepared['relations']:
        support=entry['support'];names={**history_ids,**{f'a0_{i}':weight_expr[row] for i,row in enumerate(support[:-1])}}
        constraints=[f'Equal[{tag},{entry["menu_index"]}]']+[('Greater' if row in support else 'Equal')+'['+weight_expr[row]+',0]' for row in range(k)]
        parts.append('And['+','.join(constraints+[guard(entry['fibre']['winning_relation'],names)])+']')
    relation='Or['+','.join(parts)+']';hist='{'+','.join(history_ids.values())+'}';actions='{'+','.join(weight_ids+[tag])+'}'
    mapping='{'+','.join(v+'->'+json.dumps(name) for name,v in history_ids.items())+'}'
    templates='{'+','.join(weight_expr+[tag])+'}'
    body='Module[{relation,result,export},relation='+relation+';result=G7PreferredCADSelector[relation,'+hist+','+actions+','+str(seconds)+'];export=If[result["Status"]==="SEMIALGEBRAIC_FIBRE_SELECTOR_CERTIFIED_SAME_BACKEND",G7ExportCertifiedSelector[result,'+mapping+','+templates+'],<|"Status"->"UNKNOWN_SELECTOR_EXTRACTION"|>];StringReplace[ExportString[<|"Version"->$Version,"SelectorStatus"->result["Status"],"Export"->export,"Coverage"->Lookup[result,"Coverage",False],"Soundness"->Lookup[result,"Soundness",{}],"RawCAD"->ToString[Lookup[result,"RawCAD",Lookup[result,"Raw",Missing["Unavailable"]]],InputForm]|>,"RawJSON"],{"\\n"->"","\\t"->""}]]'
    priority_order=sorted(range(len(prepared['configured_supports'])),key=lambda i:(-len(prepared['configured_supports'][i]),i))
    ranks={i:rank for rank,i in enumerate(priority_order)}
    priority='g7DeclaredMenuPriority=<|'+','.join(str(i)+'->'+str(ranks[i]) for i in range(len(ranks)))+'|>;'
    needle='good=Select[points,#["Guard"]=!=False&];'
    replacement=needle+'\n If[!And@@(IntegerQ[Last[actions]/.#["Rules"]] && KeyExistsQ[g7DeclaredMenuPriority,Last[actions]/.#["Rules"]]& /@ good),Return[<|"Status"->"UNKNOWN_NONCONSTANT_CONFIGURED_SUPPORT"|>]];\n good=SortBy[good,g7DeclaredMenuPriority[Last[actions]/.#["Rules"]]&];'
    if needle not in selector_source:raise ValueError('No recognized inherited selector ordering boundary.')
    selector_source=selector_source.replace(needle,replacement)
    return priority+'\n'+selector_source+'\n'+export_source+'\n'+body

def run():
    from provider_models import models
    root=Path(__file__).resolve().parent
    result=prepare(models(),[{'support':[0],'weights':['1','0']}],[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
    (root/'PREPARED-TERMINAL-REQUEST.json').write_text(json.dumps(result,indent=2)+'\n')
    assert result['status']=='COMPLETE_DECLARED_AFFINE_TERMINAL_MENU_RELATIONS',result.get('reason')
    combined=(root/'actual-affine-terminal-cad-selector-principal-root.wl').read_text()
    export=combined[combined.index('(* Exact AST export'):combined.rindex('Module[{relation,result,export}')]
    query=wolfram_query(result,(root/'cad_selector_principal_root.wl').read_text(),export)
    (root/'GENERATED-REQUEST-TERMINAL-SELECTOR.wl').write_text(query)
    print(json.dumps({'status':result['status'],'complete_affordable_menu_fibres':len(result['relations']),'source_dimensions':result['source_dimensions']}))
if __name__=='__main__':run()
