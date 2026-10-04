"""Fresh exact inverse-region controls, with an independent linear oracle."""
import json
from pathlib import Path
import sympy as sp
import z3
from fourier_motzkin import project_open_cube, ProjectionLimit

ROOT = Path(__file__).resolve().parent

def contains(result, history_point):
    for cell in result['cells']:
        if any(sp.sign(factor.subs(history_point)) != sign for factor, sign in cell['signs'].items()):
            continue
        if all((expr.subs(history_point) > 0 if strict else expr.subs(history_point) >= 0)
               for expr, strict in cell['inequalities']):
            return True
    return False

def direct_exists(equations, sources, point, inequalities=()):
    symbols = {s:z3.FreshReal('independentLinearSource') for s in sources}
    def linear(expr):
        expr = sp.expand(expr.subs(point))
        constant = expr.subs({s:0 for s in sources})
        result = z3.RealVal(str(constant))
        for source in sources:
            result += z3.RealVal(str(expr.coeff(source))) * symbols[source]
        return result
    solver = z3.SolverFor('QF_LRA')
    solver.add(*[z3.And(v > 0, v < 1) for v in symbols.values()])
    solver.add(*[linear(eq)==0 for eq in equations])
    solver.add(*[linear(expr)>0 if strict else linear(expr)>=0 for expr,strict in inequalities])
    result = solver.check()
    assert result != z3.unknown
    return result == z3.sat

def main():
    x, z, gamma = sp.symbols('x z gamma')
    a, b = sp.symbols('a b')
    results=[]
    def check(label, equations, sources, history, points, inequalities=()):
        projected = project_open_cube(equations, sources, history, inequalities)
        for point in points:
            assert contains(projected, point)==direct_exists(equations,sources,point,inequalities), (label,point,projected)
        results.append({'control':label,'rational_history_points':len(points),'sign_cells':len(projected['cells'])})
    check('unobserved_shared_nuisance', [x-a], [x,gamma], [a], [{a:sp.Rational(i,6)} for i in range(-1,8)])
    check('two_parameter_open_cube', [x+z-a,x-z-b], [x,z], [a,b],
          [{a:sp.Rational(i,3),b:sp.Rational(j,3)} for i in range(8) for j in range(-4,5)])
    rank_eq=[(2*a-1)*x+a-b]
    points=[{a:sp.Rational(i,8),b:sp.Rational(j,8)} for i in range(1,8) for j in range(9)]
    check('reachable_rank_zero_and_free_source',rank_eq,[x,gamma],[a,b],points,[(a,True),(1-a,True)])
    projected=project_open_cube(rank_eq,[x,gamma],[a,b],[(a,True),(1-a,True)])
    assert contains(projected,{a:sp.Rational(1,2),b:sp.Rational(1,2)})
    assert not contains(projected,{a:sp.Rational(1,2),b:sp.Rational(3,8)})
    negative=[]
    for label, args, limits in [
        ('jointly_nonlinear_source',([x*z-a],[x,z],[a]),{}),
        ('source_history_identity_overlap',([x-a],[x],[x,a]),{}),
        ('floating_coefficient',([sp.Float('.5')*x-a],[x],[a]),{}),
        ('sign_cell_resource', (rank_eq,[x],[a,b]),{'max_branches':1}),
        ('pair_resource',([x-a],[x],[a]),{'max_pairs':1})]:
        try:project_open_cube(*args,**limits)
        except (ValueError,ProjectionLimit):negative.append(label)
        else:raise AssertionError('Unsupported/resource control accepted: '+label)
    out={'status':'PASS_FRESH_AFFINE_INVERSE_REGION_CONTROLS','controls':results,'negative_controls':negative,
         'independent_oracle':'Exact QF_LRA on rational history substitutions; no generic QE completeness claim',
         'old_lost_tests_reused':False,'biological_source_family_expanded':False}
    (ROOT/'FRESH-LINEAR-PROJECTION-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
