"""Source-shared terminal winning fibres by exact strict affine projection.

This implements the ALREADY accepted last-call different-target pair reduction.
It is conditional on a supplied finite affine source-model/provider contract.
It neither certifies original catalogue coverage nor solves deeper recursion.
"""
import ctypes
import json
import signal
import sympy as sp
from compile_projected_word import parsed_action
from providers.compile_leaves import canonical_source_models
from terminal_engine import validate_models
from fourier_motzkin import project_open_cube,ProjectionLimit

def constant_pivots(equations,rows,sources):
    """Exact affine substitutions ONLY at nonzero rational constant pivots.

    Every original strict source bound is already in rows and is substituted
    along with all equations. No variable pivot or division cell is omitted.
    """
    remaining=list(sources);used=0
    while True:
        chosen=None
        for v in remaining:
            for eq in equations:
                c=sp.expand(eq).coeff(v)
                if c.is_Rational and c!=0:
                    chosen=(v,eq,c);break
            if chosen is not None:break
        if chosen is None:break
        v,eq,c=chosen;value=sp.expand(-(eq-c*v)/c)
        equations=[sp.expand(e.subs(v,value)) for e in equations]
        rows=[(sp.expand(e.subs(v,value)),strict) for e,strict in rows]
        remaining.remove(v);used+=1
    return equations,rows,remaining,used

def compile_terminal_fibre(models,calls,support,row_sites,budget,
                           max_branches=256,max_pairs=2000,seconds=30):
    receipts=[];old_handler=old_timer=None
    try:
        if type(seconds) is not int or not 0<seconds<=300:raise ProjectionLimit('Invalid terminal projection runtime.')
        def timed_out(signum,frame):raise ProjectionLimit('Terminal affine projection runtime exceeded; UNKNOWN.')
        old_handler=signal.signal(signal.SIGALRM,timed_out);old_timer=signal.setitimer(signal.ITIMER_REAL,seconds)
        if not isinstance(models,(list,tuple)) or not models:raise ValueError('Nonempty finite source carrier required.')
        normalized=[]
        for model in models:
            if not isinstance(model,dict) or not isinstance(model.get('laws'),(list,tuple)) or not model['laws'] or any(not isinstance(r,(list,tuple)) or not r for r in model['laws']):
                raise ValueError('Malformed source row/response carrier.')
            if any(type(v) is not int and not isinstance(v,sp.Expr) for r in model['laws'] for v in r):
                raise ValueError('Source laws require exact symbolic polynomials, not expression text or floats.')
            normalized.append({**model,'laws':[[sp.Integer(v) if type(v) is int else v for v in r] for r in model['laws']]})
        k,q=validate_models(normalized)
        models,source_provenance=canonical_source_models(normalized)
        for model in models:
            variables=model['variables']
            for row in model['laws']:
                for law in row:
                    if variables and sp.Poly(law,*variables).total_degree()>1:raise ValueError('Jointly nonlinear source laws remain unsupported.')
                    const=sp.expand(law).subs({v:0 for v in variables})
                    coeff=[sp.expand(law).coeff(v) for v in variables]
                    if not const.is_Rational or any(not c.is_Rational for c in coeff):raise ValueError('Source affine coefficients must be rational.')
                    if const+sum(min(c,0) for c in coeff)<0:raise ValueError('Affine row is negative on part of the supplied open cube.')
        if not isinstance(calls,list) or len(calls)>120:raise ProjectionLimit('Historical word resource ceiling120 exceeded.')
        if not isinstance(support,list) or not support or len(set(support))!=len(support) or any(type(i) is not int or not 0<=i<k for i in support):raise ValueError('Malformed proposed support.')
        if not isinstance(row_sites,list) or len(row_sites)!=k or any(not isinstance(s,(list,tuple,set)) or any(not isinstance(x,str) for x in s) for s in row_sites):raise ValueError('Original site carrier mismatch.')
        if not isinstance(budget,list) or len(budget)!=3 or any(type(n) is not int or n<0 for n in budget):raise ValueError('Invalid PATH budget.')
        names={};coordinates=[];history_weights=[];history_legal=[];written=[];used_rows=set();used_sites=set()
        for step,call in enumerate(calls):
            if not isinstance(call,dict) or set(call)!={'support','weights'} or not isinstance(call['weights'],list) or len(call['weights'])!=k:raise ValueError('Historical action fields/carrier mismatch.')
            s=call['support']
            if not isinstance(s,list) or not s or len(set(s))!=len(s) or any(type(i) is not int or not 0<=i<k for i in s):raise ValueError('Malformed historical support.')
            weights=[]
            for text in call['weights']:
                value,domains=parsed_action(text,names);weights.append(value);written.extend(domains)
            history_weights.append(weights)
            for i,w in enumerate(weights):history_legal.append((w,True) if i in s else (w,False))
            # Off-support weights and normalization are equations, not weak
            # inequalities; they are added below for every same-source world.
            used_rows|=set(s)
            for i in s:used_sites|=set(row_sites[i])
            response=[]
            for j in range(q):
                h=sp.Dummy(f'g7History_step{step}_coordinate{j}');names[f'h{step}_{j}']=h;response.append(h)
            coordinates.append(response)
        new_rows=used_rows|set(support);new_sites=used_sites|set().union(*(set(row_sites[i]) for i in support))
        cost=[len(calls)+1,len(new_rows),len(new_sites)]
        if any(cost[i]>budget[i] for i in range(3)):
            return {'status':'PROPOSED_SUPPORT_NOT_PATH_AFFORDABLE','path_cost':cost,'budget':budget,'global_budget_NO_claimed':False}
        free=[sp.Dummy(f'g7Action_coordinate{i}') for i in range(len(support)-1)]
        weights=[sp.Integer(0)]*k
        for i,v in zip(support[:-1],free):weights[i]=v
        weights[support[-1]]=1-sum(free)
        parameters=[v for row in coordinates for v in row]+free
        public={v:sp.Symbol(name) for name,v in names.items()}
        public.update({v:sp.Symbol(f'a0_{i}') for i,v in enumerate(free)})
        def rational_equation(expr,eqs,rows):
            n,d=sp.fraction(sp.cancel(expr))
            if d.free_symbols-set(parameters):raise ValueError('A source-dependent rational denominator is unsupported.')
            eqs.append(sp.expand(n));rows.append((sp.expand(d*d),True))
        def rational_positive(expr,rows):
            n,d=sp.fraction(sp.cancel(expr))
            if d.free_symbols-set(parameters):raise ValueError('A source-dependent rational denominator is unsupported.')
            rows.extend([(sp.expand(n*d),True),(sp.expand(d*d),True)])
        def history_system(model):
            eqs=[];rows=[]
            for v in model['variables']:rows.extend([(v,True),(1-v,True)])
            for domain in written:
                n,d=sp.fraction(sp.cancel(domain));rows.extend([(sp.expand(n*n),True),(sp.expand(d*d),True)])
            for step,(old,observed) in enumerate(zip(history_weights,coordinates)):
                s=calls[step]['support']
                rational_equation(sum(old)-1,eqs,rows)
                for i,w in enumerate(old):
                    if i in s:rational_positive(w,rows)
                    else:rational_equation(w,eqs,rows)
                for j,h in enumerate(observed):
                    rational_equation(sum(old[i]*model['laws'][i][j] for i in range(k))-h,eqs,rows)
            return eqs,rows
        def relation(op,expr):
            if expr.free_symbols-set(public):raise ValueError('Source/auxiliary survived terminal projection.')
            return {'op':op,'left':str(expr.xreplace(public)),'right':'0'}
        def project(eqs,rows,variables,label):
            eqs,rows,remaining,count=constant_pivots(eqs,rows,variables)
            result=project_open_cube(eqs,remaining,parameters,rows,max_branches=max_branches,max_pairs=max_pairs)
            cells=[]
            for cell in result['cells']:
                guards=[relation({-1:'lt',0:'eq',1:'gt'}[sign],factor) for factor,sign in sorted(cell['signs'].items(),key=lambda p:sp.default_sort_key(p[0]))]
                guards.extend(relation('gt' if strict else 'ge',expr) for expr,strict in cell['inequalities'])
                cells.append({'op':'and','args':guards})
            receipts.append({'kind':label,'source_variables':len(variables),'constant_rational_pivots':count,'remaining_variables_FM_eliminated':len(remaining),'cells':len(cells),'peak_sign_cells':result['peak_sign_cells'],'pair_combinations':result['pair_combinations']})
            return {'op':'or','args':cells}
        domains=[]
        for i,model in enumerate(models):
            eqs,rows=history_system(model);domains.append(project(eqs,rows,model['variables'],['history',i]))
        collisions=[];pairs=[]
        for i,a in enumerate(models):
            for j in range(i+1,len(models)):
                b=models[j]
                if json.dumps(a['target'],sort_keys=True)==json.dumps(b['target'],sort_keys=True):continue
                ae,ar=history_system(a);be,br=history_system(b);eqs=ae+be;rows=ar+br
                for h in support:rational_positive(weights[h],rows)
                for coordinate in range(q):
                    rational_equation(sum(weights[row]*(a['laws'][row][coordinate]-b['laws'][row][coordinate]) for row in range(k)),eqs,rows)
                collisions.append(project(eqs,rows,a['variables']+b['variables'],['different_target_pair',i,j]));pairs.append([i,j])
        domain={'op':'or','args':domains};collision={'op':'or','args':collisions}
        legal={'op':'and','args':[relation('gt',weights[i]) for i in support]}
        winning={'op':'and','args':[domain,legal,{'op':'not','arg':collision}]}
        return {'status':'TERMINAL_AFFINE_WINNING_FIBRE_PROJECTED','history_domain':domain,'different_target_collision_relation':collision,'winning_relation':winning,'proposed_support':support,
                'action_weights':[str(w.xreplace(public)) for w in weights],'history_coordinates':list(names),'free_action_coordinates':[f'a0_{i}' for i in range(len(free))],'path_cost':cost,'budget':budget,
                'different_target_pairs':pairs,'projection_receipts':receipts,'source_shared_within_entire_history':True,'rival_assignments_separate':True,'written_domains_retained':True,
                'source_identity_provenance':source_provenance,'method':'existing last-call pair separation plus strict affine FM and exact rational constant pivots',
                'source_provider_admission':'conditional on separately pinned complete finite source-model contract','generic_recursive_policy_extracted':False,'unknown_size_G3_G4_claimed':False}
    except (ValueError,TypeError,KeyError,IndexError,AttributeError,SyntaxError,ArithmeticError,RecursionError,MemoryError,ctypes.ArgumentError,sp.PolynomialError) as error:
        return {'status':'UNKNOWN_TERMINAL_AFFINE_PROJECTION','reason':str(error),'partial_projection_receipts':receipts,'global_budget_NO_claimed':False}
    finally:
        if old_handler is not None:
            signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,old_handler)
            if old_timer and old_timer[0]>0:signal.setitimer(signal.ITIMER_REAL,*old_timer)
