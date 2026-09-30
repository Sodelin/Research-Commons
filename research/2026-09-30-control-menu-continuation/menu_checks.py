"""Exact finite controls for ideal hybrid intervention menus.

No biological simulation, Lean proof, or network planarity algorithm is run.
The padded gadget's source admission is proved in REPORT.md.
"""
from fractions import Fraction
from itertools import combinations, product
from math import comb, ceil, log2
import json
from pathlib import Path


def patterns(row, i, j):
    if row[i] is None and row[j] is None:
        return set()
    return {(a, b) for a, b in product((0, 1), repeat=2)
            if (row[i] is None or row[i] == a)
            and (row[j] is None or row[j] == b)}


def covers(rows, r):
    return all(set().union(*(patterns(row, i, j) for row in rows))
               == set(product((0, 1), repeat=2))
               for i, j in combinations(range(r), 2))


def single_menu(r):
    return [tuple(a if k == i else None for k in range(r))
            for i in range(r-1) for a in (0, 1)]


def two_menu(r):
    if r == 2:
        return single_menu(r)
    if r == 3:
        return [(0,0,None),(1,None,0),(None,1,1)]
    k = r-1
    return [tuple(0 if i == t else 1 if i == (t+1) % k else None
                  for i in range(r)) for t in range(k)]


def full_count(r):
    if r <= 1:
        return 1 if r == 0 else 2
    m = 4
    while comb(m-1, m//2-1) < r:
        m += 1
    return m


def full_array(r):
    m = full_count(r)
    if r == 0:
        return [()]
    if r == 1:
        return [(0,), (1,)]
    subs = list(combinations(range(1, m), m//2-1))[:r]
    return [tuple(int(row == 0 or row in sub) for sub in subs)
            for row in range(m)]


def trinomial(m):
    return sum(comb(m,2*k)*comb(2*k,k) for k in range(m//2+1))


def partial_count(r):
    m = 1
    while (trinomial(m)+1)//2 < r:
        m += 1
    return m


def partial_array(r):
    m = partial_count(r)
    words = []
    for x in product(range(3),repeat=m):
        if sum(x) != m:
            continue
        bar = tuple(2-a for a in x)
        if x <= bar:
            words.append(x)
            if len(words) == r:
                break
    assert len(words) == r
    return [tuple(None if x[t] == 1 else x[t]//2 for x in words)
            for t in range(m)]


def gadget(r, active=(0, 1), required=(1, 1)):
    # Parent option "required" is the unique rare-target option.
    edges = [('R','D'), ('R','v3'), ('v3','v2'), ('v2','v1'),
             ('v1','v0'), ('HA','A'), ('HC','C')]
    hybrid = {active[0]: ('HA', {required[0]: 'v1', 1-required[0]: 'v3'}),
              active[1]: ('HC', {required[1]: 'v2', 1-required[1]: 'v0'})}
    previous = 'v0'
    for i in range(r):
        if i in active:
            continue
        u, h = f'u{i}', f'H{i}'
        edges += [(previous, u)]
        hybrid[i] = (h, {0:u, 1:u})  # parallel arcs, distinguished by bit
        previous = h
    edges.append((previous, 'B'))
    return edges, hybrid


def raw_degrees(edges, hybrid):
    raw = edges + [(parent, h) for h, opts in hybrid.values()
                   for parent in opts.values()]
    vs = {v for e in raw for v in e}
    indeg = {v:sum(b == v for a,b in raw) for v in vs}
    outdeg = {v:sum(a == v for a,b in raw) for v in vs}
    assert (indeg['R'], outdeg['R']) == (0, 2)
    for v in vs - {'R', 'A', 'B', 'C', 'D'}:
        assert (indeg[v], outdeg[v]) in {(1,2),(2,1)}
    for v in 'ABCD':
        assert (indeg[v], outdeg[v]) == (1,0)
    remaining = set(vs)
    removed = set()
    while remaining:
        ready = {v for v in remaining if all(a in removed for a,b in raw if b == v)}
        assert ready, 'DAG has a directed cycle'
        removed |= ready
        remaining -= ready


def quartet(edges):
    adj = {}
    for a,b in edges:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    assert len(edges) == len(adj)-1
    def distance(a,b):
        todo = [(a,None,0)]
        while todo:
            v, prev, d = todo.pop()
            if v == b:
                return d
            todo.extend((w,v,d+1) for w in adj[v] if w != prev)
        raise AssertionError('disconnected tree')
    sums = [distance('A','B')+distance('C','D'),
            distance('A','C')+distance('B','D'),
            distance('A','D')+distance('B','C')]
    low = min(sums)
    assert sums.count(low) == 1
    others = [x for x in sums if x != low]
    assert others[0] == others[1]
    return sums.index(low), (others[0]-low)//2


def switching_records(r, active=(0,1), required=(1,1)):
    base, hs = gadget(r, active, required)
    raw_degrees(base, hs)
    result = []
    for bits in product((0,1), repeat=r):
        selected = base + [(hs[i][1][bits[i]], hs[i][0]) for i in range(r)]
        q, length = quartet(selected)
        rare = all(bits[i] == a for i,a in zip(active, required))
        assert q == (0 if rare else 2)
        assert length >= 1
        result.append((bits,q,length))
    return result


def cf(records, row, ps):
    result = [Fraction(0) for _ in range(3)]
    mass = [Fraction(0) for _ in range(3)]
    for bits,q,length in records:
        if any(a is not None and bits[i] != a for i,a in enumerate(row)):
            continue
        weight = Fraction(1)
        for i,a in enumerate(row):
            if a is None:
                weight *= ps[i] if bits[i] else 1-ps[i]
        x = Fraction(1,2)**length  # each original edge length = log(2)
        for t in range(3):
            result[t] += weight*(x/3 + (1-x if t == q else 0))
        mass[q] += weight
    assert sum(result) == 1 and sum(mass) == 1
    return result, mass


def main():
    result = {'kind':'exact finite analytical/graph controls, not empirical evidence'}
    minima = {}
    for r in range(2,7):
        literals = [(i,a) for i in range(r) for a in (0,1)]
        valid = []
        for mask in range(1 << (2*r)):
            chosen = {literals[k] for k in range(2*r) if mask >> k & 1}
            if all((i,a) in chosen or (j,b) in chosen
                   for i,j in combinations(range(r),2) for a,b in product((0,1),repeat=2)):
                valid.append(len(chosen))
        minima[r] = min(valid)
        assert minima[r] == 2*r-2 and covers(single_menu(r),r)
    result['single_control_exhaustive_minima'] = minima
    result['single_menu_coverage_r2_to_100'] = all(covers(single_menu(r),r) for r in range(2,101))
    partial = [(0,0,None,None), (1,None,0,None), (None,1,1,None)]
    assert covers(partial,4)
    result['three_row_partial_array_r4_b2'] = partial
    assert all(covers(two_menu(r),r) for r in range(2,101))
    result['two_control_cycle_coverage_r2_to_100'] = True
    result['full_array_counts'] = {r:full_count(r) for r in (2,3,4,10,100,1000,10000,1000000)}
    result['optimal_partial_counts'] = {r:partial_count(r) for r in (2,3,4,10,100,1000,10000,1000000)}
    result['optimal_partial_array_r10'] = partial_array(10)
    assert all(covers(partial_array(r),r) for r in range(2,129))
    result['central_rank_partial_coverage_r2_to_128'] = True
    pair_checks = 0
    for r in range(2,129):
        rows = full_array(r)
        assert covers(rows,r)
        pair_checks += comb(r,2)
    result['full_arrays_r2_to_128_column_pairs_checked'] = pair_checks
    result['full_array_r10'] = full_array(10)
    graphs = 0
    switchings = 0
    readouts = 0
    g = Fraction(1,8)
    for r in range(2,7):
        for active in combinations(range(r),2):
            for required in product((0,1),repeat=2):
                records = switching_records(r,active,required)
                graphs += 1
                switchings += len(records)
                ps = [Fraction(1,2)]*r
                for i,a in zip(active,required):
                    ps[i] = g if a else 1-g
                for rows, delta in [(single_menu(r),g/2),(two_menu(r),g/2),
                                    (partial_array(r),g/2),
                                    (full_array(r),Fraction(1,2))]:
                    contrasts = [Fraction(0)]*3
                    masses = [Fraction(0)]*3
                    for row in rows:
                        probs,mass = cf(records,row,ps)
                        readouts += 1
                        contrasts = [max(contrasts[t],probs[t]-min(probs)) for t in range(3)]
                        masses = [max(masses[t],mass[t]) for t in range(3)]
                    assert masses[0] >= (1 if rows == full_array(r) else g)
                    assert contrasts[0] >= delta
                    assert contrasts[1] == 0 and contrasts[2] > 0
    result['padded_graphs_checked'] = graphs
    result['padded_switching_trees_checked'] = switchings
    result['exact_common_inheritance_environment_readouts'] = readouts
    result['not_run'] = ['Lean','biological experiment','independent-lineage coalescent simulation',
                         'automated planarity/source-admission proof','efficient general decoder']
    path = Path(__file__).with_name('checks.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
