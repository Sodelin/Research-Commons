#!/usr/bin/env python3
"""Bounded exact diagnostics for the accompanying general hand proof.

The 4-vertex enumeration checks a combinatorial lemma. The 3-qubit test
checks one noncommuting auxiliary reference, not actual Redfield dynamics.
No stochastic sampling, numerical eigensolver, or bath truncation is used.
"""
from itertools import combinations, product
import sympy as s

checks = 0
def check(name, statement):
    global checks
    assert statement, name
    checks += 1
    print('PASS', name)

def components(mask, adj, n):
    left = {i for i in range(n) if mask >> i & 1}
    out = []
    while left:
        reached = {left.pop()}
        frontier = set(reached)
        while frontier:
            nxt = set().union(*(adj[i] for i in frontier)) & left
            left -= nxt
            reached |= nxt
            frontier = nxt
        out.append(sum(1 << i for i in reached))
    return out

def hulls(adj, root, n):
    possible = [(u, (u & ~root).bit_count()) for u in range(1 << n)
                if u & root == root
                and all(c & root for c in components(u, adj, n))]
    return {v: min(cost for u, cost in possible if u & v == v)
            for v in range(1 << n)
            if any(u & v == v for u, _ in possible)}

n = 4
edges = list(combinations(range(n), 2))
comparisons = 0
root_cases = 0
for edge_mask in range(1 << len(edges)):
    adj = [set() for _ in range(n)]
    for j, (a, b) in enumerate(edges):
        if edge_mask >> j & 1:
            adj[a].add(b)
            adj[b].add(a)
    cliques = [z for z in range(1, 1 << n)
               if all(b in adj[a] for a, b in combinations(
                   [i for i in range(n) if z >> i & 1], 2))]
    for root in range(1, 1 << n):
        costs = hulls(adj, root, n)
        root_cases += 1
        assert costs[0] == 0
        assert all(costs[v] == 0 for v in costs if v & ~root == 0)
        for z in cliques:
            for u in costs:
                if not u & z:
                    continue
                for v in costs:
                    if not v & z or u & ~z != v & ~z:
                        continue
                    assert abs(u.bit_count()-v.bit_count()) <= z.bit_count()-1
                    assert costs[v]-costs[u] <= (v & ~u & ~root).bit_count()
                    assert abs(costs[u]-costs[v]) <= z.bit_count()-1
                    comparisons += 1
check('rooted-hull ratio on every graph/root/clique on four vertices',
      root_cases == 960 and comparisons > 0)
print('Exact combinatorial cases:', root_cases, 'support comparisons:', comparisons)

# Pauli products: labels 0=I, 1=X, 2=Y, 3=Z.
mul = {(i, 0): (s.S.One, i) for i in range(4)}
mul.update({(0, i): (s.S.One, i) for i in range(4)})
mul.update({(i, i): (s.S.One, 0) for i in range(1, 4)})
for i, j, k in [(1, 2, 3), (2, 3, 1), (3, 1, 2)]:
    mul[i, j] = (s.I, k)
    mul[j, i] = (-s.I, k)

def multiply(p, q):
    local = [mul[a, b] for a, b in zip(p, q)]
    return s.prod(a for a, _ in local), tuple(b for _, b in local)

paulis = list(product(range(4), repeat=3))
index = {p: j for j, p in enumerate(paulis)}
terms = [(s.Rational(1, 2), (1, 3, 0)),
         (s.Rational(1, 2), (0, 2, 3))]
check('reference Hamiltonian terms do not commute',
      multiply(terms[0][1], terms[1][1])[0]
      != multiply(terms[1][1], terms[0][1])[0])
incidence = [sum(abs(c) for c, p in terms if p[i]) for i in range(3)]
check('original incidence bound h=1 with all b_p=1', max(incidence) == 1)

C = s.zeros(64)
for col, p in enumerate(paulis):
    for coeff, hz in terms:
        left, result = multiply(hz, p)
        right, result2 = multiply(p, hz)
        assert result == result2
        C[index[result], col] += s.I * coeff * (left-right)
check('coherent matrix skew-adjoint', C.T == -C)
check('both coherent vacuum columns and rows vanish',
      C[:, 0] == s.zeros(64, 1) and C[0, :] == s.zeros(1, 64))
N = s.diag(*[sum(bool(v) for v in p) for p in paulis])
D = s.zeros(64)
for col, p in enumerate(paulis):
    for site in range(3):
        for axis in (1, 2, 3):
            anchor = tuple(axis if j == site else 0 for j in range(3))
            phase, intermediate = multiply(anchor, p)
            phase2, result = multiply(intermediate, anchor)
            D[index[result], col] += 2*phase*phase2
            D[col, col] -= 2
check('all nine noise channels give D0*=-8N', D == -8*N)

# X={site 0}; path graph. a=b=log 2, hence d=log 4 and lambda=2.
adj = [{1}, {0, 2}, {1}]
cost = hulls(adj, 1, 3)
supports = [sum(1 << i for i, v in enumerate(p) if v) for p in paulis]
weights = [s.Integer(2)**(v.bit_count()+cost[v]) for v in supports]
W = s.diag(*weights)
Winv = s.diag(*[1/v for v in weights])
K = -D-C
KW = W*K*Winv
lam = s.Integer(8)-2*(s.Integer(4)-1)
check('explicit localized-form margin lambda=2', lam == 2)
M = (KW+KW.T)/2-lam*N
gersh = [M[i, i]-sum(abs(M[i, j]) for j in range(64) if i != j)
         for i in range(64)]
check('weighted form minus lambda N is exactly diagonally dominant',
      all(v >= 0 for v in gersh))
check('weighted scalar row and column remain zero',
      KW[:, 0] == s.zeros(64, 1) and KW[0, :] == s.zeros(1, 64))
check('local rooted initial support has hull cost zero',
      all(cost[v] == 0 for v in (0, 1)))

# The half-gap choice uses exp(d)=3, independently of k>1.
g, h = s.symbols('g h', positive=True)
check('half-gap margin at h=g/8',
      s.simplify((g-2*h*(3-1)).subs(h, g/8)-g/2) == 0)
check('source exponent test is nonpositive starting at k=3',
      1-(4**(3-1)-1)/4 < 0)
print('Exact nonzero-sector Gershgorin minimum:', min(gersh[1:]))
print('TOTAL PASS:', checks)
