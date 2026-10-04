"""Export the ACTUAL recursive AST and free history/action carrier to Wolfram.

No hand-entered desired winning relation replaces the source-derived formula.
Alpha-renaming handles quantified source/action/response identities explicitly.
"""
import z3


def to_wolfram(expression):
    names = {}; serial = 0
    def fresh():
        nonlocal serial
        serial += 1
        return 'g7var' + str(serial)
    def go(e, bound):
        if z3.is_var(e):
            return bound[z3.get_var_index(e)]
        if z3.is_true(e): return 'True'
        if z3.is_false(e): return 'False'
        if z3.is_rational_value(e):
            value = e.as_fraction()
            return str(value.numerator) if value.denominator == 1 else '('+str(value.numerator)+'/'+str(value.denominator)+')'
        if isinstance(e, z3.AlgebraicNumRef):
            coeff = [x.as_fraction() for x in e.poly()]
            terms = ['('+str(c)+')*Slot[1]^'+str(i) for i,c in enumerate(coeff) if c]
            return 'Root[Function['+'+'.join(terms)+'],'+str(e.index())+']'
        if z3.is_quantifier(e):
            vv = [fresh() for _ in range(e.num_vars())]
            body = go(e.body(), list(reversed(vv)) + bound)
            return ('ForAll' if e.is_forall() else 'Exists')+'[{'+','.join(vv)+'},'+body+']'
        if not z3.is_app(e): raise ValueError('Unsupported recursive AST')
        kind = e.decl().kind()
        if kind == z3.Z3_OP_UNINTERPRETED and e.num_args() == 0:
            key = e.get_id()
            if key not in names: names[key] = fresh()
            return names[key]
        args = [go(a,bound) for a in e.children()]
        functions = {z3.Z3_OP_AND:'And',z3.Z3_OP_OR:'Or',z3.Z3_OP_NOT:'Not',z3.Z3_OP_IMPLIES:'Implies',
                     z3.Z3_OP_EQ:'Equal',z3.Z3_OP_DISTINCT:'Unequal',z3.Z3_OP_LT:'Less',z3.Z3_OP_LE:'LessEqual',
                     z3.Z3_OP_GT:'Greater',z3.Z3_OP_GE:'GreaterEqual',z3.Z3_OP_ADD:'Plus',z3.Z3_OP_MUL:'Times',
                     z3.Z3_OP_POWER:'Power'}
        if kind in functions: return functions[kind]+'['+','.join(args)+']'
        if kind == z3.Z3_OP_UMINUS: return 'Times[-1,'+args[0]+']'
        if kind == z3.Z3_OP_SUB: return 'Plus['+args[0]+',Times[-1,'+args[1]+']]'
        if kind == z3.Z3_OP_DIV: return 'Times['+args[0]+',Power['+args[1]+',-1]]'
        if kind == z3.Z3_OP_ITE: return 'If['+','.join(args)+']'
        if kind == z3.Z3_OP_TO_REAL: return args[0]
        raise ValueError('Unsupported arithmetic/logical operator: '+str(e.decl()))
    result = go(expression, [])
    return result, names


def winning_action_relation(engine, history, remaining_calls, used_rows, used_sites, support):
    """Expose a support's unquantified real action fibre at its actual state."""
    rows = set(used_rows) | set(support)
    sites = set(used_sites) | set().union(*(engine.row_sites[i] for i in support))
    if remaining_calls < 1 or len(rows) > engine.row_cap or len(sites) > engine.site_cap:
        return [], [], z3.BoolVal(False)
    variables, weights, legal = engine.action(support)
    if remaining_calls == 1:
        collisions = []
        for i,j in engine.pairs:
            if history:
                base = engine.pair_collision(i,j,[],weights,[legal])
                gg=z3.Goal();gg.add(base)
                try: simplified=z3.TryFor(z3.Tactic('qe'),engine.terminal_pair_qe_ms)(gg).as_expr()
                except z3.Z3Exception: simplified=base
                if z3.is_false(z3.simplify(simplified)):
                    collisions.append(z3.BoolVal(False))
                    continue
            raw = engine.pair_collision(i,j,history,weights,[legal])
            goal=z3.Goal();goal.add(raw)
            try: reduced=z3.TryFor(z3.Tactic('qe'),engine.terminal_pair_qe_ms)(goal).as_expr()
            except z3.Z3Exception: reduced=raw
            collisions.append(reduced)
        return variables,weights,z3.And(legal,*[z3.Not(c) for c in collisions])
    response=[z3.FreshReal('selectorNextOriginalResponse') for _ in range(engine.q)]
    continuation=engine.win(history+[(weights,response)],remaining_calls-1,rows,sites)
    return variables,weights,z3.And(legal,z3.ForAll(response,continuation))
