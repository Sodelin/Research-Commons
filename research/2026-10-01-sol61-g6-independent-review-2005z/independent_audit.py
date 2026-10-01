"""Independent exact component audit for SOL61-G6-INDEPENDENT-REVIEW-20261001.

This does not import the contributor's checker. It is not the full source
catalogue, chronology compiler, statistical engine, or formal proof.
"""
from collections import Counter, defaultdict
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations, product
from math import comb, prod
from pathlib import Path
import hashlib
import json
import platform
import random
import z3

counts = Counter()
details = {}

def verify(value, label):
    if not value:
        raise AssertionError(label)
    counts[label] += 1

def canonical(trees):
    return tuple(sorted(trees, key=repr))

@lru_cache(None)
def jump_outcomes(state, jumps):
    if jumps == 0:
        return {state: F(1)}
    out = defaultdict(F)
    for i, j in combinations(range(len(state)), 2):
        merged = canonical((state[i], state[j]))
        nxt = canonical([x for t, x in enumerate(state) if t not in (i, j)] + [merged])
        for result, prob in jump_outcomes(nxt, jumps - 1).items():
            out[result] += prob / comb(len(state), 2)
    return dict(out)

@lru_cache(None)
def edge(state, survival):
    k = len(state)
    if k <= 1:
        return {state: F(1)}
    out = defaultdict(F)
    for remaining in range(1, k + 1):
        numerator = prod(comb(j, 2) for j in range(remaining + 1, k + 1))
        mass = numerator * sum((survival ** comb(j, 2) /
            prod(F(comb(l, 2) - comb(j, 2)) for l in range(remaining, k + 1) if l != j)
            for j in range(remaining, k + 1)), F(0))
        for result, prob in jump_outcomes(state, k - remaining).items():
            out[result] += mass * prob
    return dict(out)

def independent_bigon(k, x, y, g):
    out = defaultdict(F)
    for mask in range(1 << k):
        left = canonical([i for i in range(k) if mask & (1 << i)])
        right = canonical([i for i in range(k) if not mask & (1 << i)])
        weight = g ** len(left) * (1 - g) ** len(right)
        for a, pa in edge(left, x).items():
            for b, pb in edge(right, y).items():
                out[canonical(a + b)] += weight * pa * pb
    return dict(out)

def tv(a, b):
    return sum((abs(a.get(s, F(0)) - b.get(s, F(0))) for s in a.keys() | b.keys()), F(0)) / 2

def forest_tests():
    grid = [F(1, 1000), F(1, 7), F(1, 2), F(6, 7), F(999, 1000)]
    fixtures = list(product(grid, repeat=3))
    # Five-lineage tests include extreme inheritance and near-zero/one hazards.
    five_fixtures = [(grid[i], grid[j], grid[(2*i+j) % len(grid)])
                     for i in range(len(grid)) for j in range(len(grid))]
    largest = F(0)
    for k in range(2, 6):
        C = comb(k, 2)
        A = max(F(1), F(3, 2) * comb(k, 3) + 27 * comb(k, 4))
        D = 2 * C * A
        for x, y, g in (five_fixtures if k == 5 else fixtures):
            actual = independent_bigon(k, x, y, g)
            q = g*g*(1-x) + (1-g)**2*(1-y)
            ordinary = edge(tuple(range(k)), 1-q)
            err = tv(actual, ordinary)
            verify(sum(actual.values()) == 1 and min(actual.values()) >= 0, 'forest_normalization')
            verify(err*err <= D*D*q**3, 'independent_weak_bound')
            largest = max(largest, err*err/(D*D*q**3))
    details['forest_fixture_count'] = 400
    details['largest_squared_bound_ratio'] = str(largest)
    details['forest_outcomes_at_k5'] = len(edge(tuple(range(5)), F(1, 2)))

def guard_tests():
    rng = random.Random(20261001)
    for length in range(21):
        pieces = [F(rng.randint(1, 100), rng.randint(1, 30)) for _ in range(2*length+1)]
        ages = [F(0)]
        for width in pieces:
            ages.append(ages[-1] + width)
        bigons = [(ages[2*i+1], ages[2*i+2]) for i in range(length)]
        choices = sorted(set(ages + [(a+b)/2 for a,b in zip(ages, ages[1:])]))
        for _ in range(60):
            cuts = sorted(rng.sample(choices, min(len(choices), rng.randint(0, 12))))
            marked = set()
            for c in cuts:
                for i, (a,b) in enumerate(bigons):
                    if a <= c <= b:
                        marked.add(i)
                for i in range(length+1):
                    lo = ages[0] if i == 0 else bigons[i-1][1]
                    hi = ages[-1] if i == length else bigons[i][0]
                    if lo < c < hi:
                        marked.update(j for j in (i-1,i) if 0 <= j < length)
            verify(len(marked) <= 2*len(cuts), 'nonuniform_guard_count')
            unmarked = [i for i in range(length) if i not in marked]
            runs = []
            for i in unmarked:
                if not runs or runs[-1][-1] != i-1:
                    runs.append([])
                runs[-1].append(i)
            verify(len(runs) <= 2*len(cuts)+1, 'nonuniform_run_count')
            for run in runs:
                lo = ages[0] if run[0] == 0 else bigons[run[0]-1][1]
                hi = ages[-1] if run[-1] == length-1 else bigons[run[-1]+1][0]
                verify(not any(lo < c < hi for c in cuts), 'nonuniform_no_cut_inside_run')
    details['nonuniform_guard_fixtures'] = 1260

def positive_tests():
    for K in range(1, 61):
        for X in (F(1, 10**6), F(1, 5), F(1, 2), F(999999, 10**6)):
            a = 1 - (1-X)/F(4*K+1)
            residual = X/a**(2*K)
            verify(0 < residual < 1 and 0 < a < 1, 'positive_common_reconstruction')
            verify(residual*a**(2*K) == X, 'exact_common_baseline')
    # Retiming independent desired coalescent lengths on parallel arms.
    for K in range(31):
        gap = F(103, 97)
        unit = gap/(2*K+1)
        for j in range(2*K+1):
            ds = (F(j+1,19),) if j%2 == 0 else (F(j+1,19), F(j+3,23))
            for duration in ds:
                rate = duration/unit
                verify(rate > 0 and rate*unit == duration, 'positive_same_endpoint_embedding')

def algebra_tests():
    r, r1, r2, a, g, x, A, B = z3.Reals('r r1 r2 a g x A B')
    q = lambda v: z3.RealVal(str(v))
    cases = {
      'shared_equal_epochs_conflict': (z3.And(r>0,r>=1,r<=q('1.1'),r>=2,r<=q('2.1')), False),
      'independent_rate_relaxation_accepts': (z3.And(r1>0,r2>0,r1>=1,r1<=q('1.1'),r2>=2,r2<=q('2.1')), True),
      'shared_rate_variable_age_feasible': (z3.And(r>0,a>q('2.9'),a<q('3.1'),r>=1,r<=q('1.1'),r*(a-1)>=2,r*(a-1)<=q('2.1')), True),
      'unbounded_age_small_rate_feasible': (z3.And(r>0,a>10**6,r*a>=1,r*a<=q('1.1')), True),
      'shared_inheritance_rows_conflict': (z3.And(g>0,g<1,g>=q('.1'),g<=q('.2'),g>=q('.8'),g<=q('.9')), False),
      'positive_edge_tied_endpoints_conflict': (z3.And(a>1,a==1), False),
      'known_rate_doubling_feasible': (z3.And(r>0,r>=1,r<=q('1.1'),2*r>=2,2*r<=q('2.1')), True),
      'known_rate_doubling_conflict': (z3.And(r>0,r>=1,r<=q('1.1'),2*r>=3,2*r<=q('3.1')), False),
      'triple_bound_counterexample': (z3.And(x>=0,x<=1,1-q('1.5')*x+q('.5')*x**3 > q('1.5')*(1-x)**2), False),
      'four_lineage_bound_counterexample': (z3.And(x>=0,x<=1,(1-x**3)**2 > 9*(1-x)**2), False),
      'two_arm_bound_counterexample': (z3.And(A>=0,B>=0,9*A*A+9*B*B+2*A*B > 9*(A+B)**2), False),
    }
    results = {}
    for name, (formula, feasible) in cases.items():
        solver = z3.SolverFor('QF_NRA')
        solver.set(timeout=10000)
        solver.add(formula)
        result = solver.check()
        verify(result == (z3.sat if feasible else z3.unsat), 'exact_nonlinear_real_query')
        results[name] = str(result)
    details['exact_solver_results'] = results

def noise_tests():
    # Three-outcome simplex: exact midpoint overlap includes equality, with no
    # coordinate-sup/TV conflation. This is finite verification of a hand proof.
    simplex = [(F(a, 6),F(b,6),F(6-a-b,6)) for a in range(7) for b in range(7-a)]
    dist = lambda p,q: sum(abs(a-b) for a,b in zip(p,q))/2
    for p, q in product(simplex, repeat=2):
        d = dist(p,q)
        midpoint = tuple((a+b)/2 for a,b in zip(p,q))
        verify(dist(p,midpoint) == d/2 == dist(q,midpoint), 'tv_midpoint_exact_boundary')
        for beta in (F(0),F(1,12),F(1,4),F(1,2)):
            verify((d <= 2*beta) == (dist(p,midpoint)<=beta and dist(q,midpoint)<=beta), 'tv_closed_ball_overlap')

def main():
    guard_tests()
    positive_tests()
    algebra_tests()
    noise_tests()
    forest_tests()
    here = Path(__file__)
    receipt = {'status':'PASS','session':'SOL61-G6-INDEPENDENT-REVIEW-20261001-2005Z',
       'python':platform.python_version(),'z3':z3.get_version_string(),
       'arithmetic':'exact rationals and exact nonlinear-real satisfiability',
       'counts':dict(counts),'total_checks':sum(counts.values()),'details':details,
       'script_sha256':hashlib.sha256(here.read_bytes()).hexdigest(),
       'not_executed':['full source catalogue','general hazard-cell enumeration',
         'complete calendar compiler','integrated inference engine','Lean verification']}
    (here.parent/'independent-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__ == '__main__':
    main()
