"""Exact source/control check; no finite-prefix or G4 impossibility claim."""
from pathlib import Path
from dataclasses import replace
from fractions import Fraction as F
from itertools import product
import hashlib
import json
import sys
import platform

ROOT = Path(__file__).resolve().parents[4]
UPSTREAM = ROOT / 'research/2026-10-01-g4-admitted-testers-0819z'
sys.path.insert(0, str(UPSTREAM))
from source_checks import Edge, Source, compile_source
from forest_algebra import leaves
import networkx


def fixture(s):
    kinds = {'R': 'root', **{v: 'tree' for v in ('U', 'P0', 'P1', 'Q')},
             **{v: 'hybrid' for v in ('HA', 'HC')},
             **{v: 'leaf' for v in 'ABCD'}}
    arcs = [('ru', 'R', 'U'), ('rq', 'R', 'Q'),
            ('u0', 'U', 'P0'), ('u1', 'U', 'P1'),
            ('a0', 'P0', 'HA'), ('c0', 'P0', 'HC'),
            ('a1', 'P1', 'HA'), ('d', 'P1', 'D'),
            ('c1', 'Q', 'HC'), ('b', 'Q', 'B'),
            ('a', 'HA', 'A'), ('c', 'HC', 'C')]
    xs = {'a': F(1, 4)/s, 'a0': F(1, 2)*s, 'a1': F(1, 3)*s}
    return Source(kinds, {v: v for v in 'ABCD'},
                  tuple(Edge(k, u, v, xs.get(k, F(1, 2))) for k, u, v in arcs),
                  {'HA': F(2, 5), 'HC': F(3, 7)})


def profile(source, bits):
    removed = set()
    for h, bit in bits.items():
        inc = sorted((e for e in source.edges if e.v == h), key=lambda e: e.name)
        removed.add(inc[1-bit].name)

    def descend(v):
        if v in source.taxa:
            return F(1), source.taxa[v]
        children = []
        for e in source.edges:
            if e.u != v or e.name in removed:
                continue
            got = descend(e.v)
            if got is not None:
                x, tree = got
                children.append((e.x*x, tree))
        if not children:
            return None
        if len(children) == 1:
            return children[0]
        return F(1), tuple(sorted(children, key=repr))
    return descend('R')


def clades(prof):
    result = set()
    def walk(t):
        if isinstance(t, str):
            s = frozenset([t])
        else:
            s = frozenset().union(*(walk(c) for x, c in t))
        result.add(s)
        return s
    walk(prof[1])
    return result


def prune(t, keep):
    if isinstance(t, int):
        return t if t in keep else None
    a, b = (prune(c, keep) for c in t)
    if a is None:
        return b
    if b is None:
        return a
    return a, b


def crossed(law):
    return sum((p for t, p in law.items()
                if any(set(leaves(c)) == {0, 2}
                       for c in prune(t, {0, 1, 2}))), F(0))


def main():
    ss = [fixture(F(1)), fixture(F(2, 3))]
    admission = [s.validate() for s in ss]
    profiles = [[profile(s, dict(zip(('HA', 'HC'), bits)))
                 for bits in product((0, 1), repeat=2)] for s in ss]
    assert profiles[0] == profiles[1]
    common_clades = set.intersection(*(clades(p) for p in profiles[0]))
    assert common_clades == {frozenset(x) for x in ('A', 'B', 'C', 'D', 'ABCD')}
    allocation = {'A': 2, 'B': 1, 'C': 1, 'D': 1}
    common = [compile_source(s, allocation, 'common') for s in ss]
    assert common[0] == common[1]
    independent = [crossed(compile_source(s, allocation, 'independent')) for s in ss]
    g = F(2, 5)
    predicted = []
    for scale in (F(1), F(2, 3)):
        x0, x1 = F(1, 4)*scale, F(1, 6)*scale
        d2 = g*g*x0 + (1-g)**2*x1 + 2*g*(1-g)
        predicted.append(F(1, 4)/scale * F(1, 2) * d2 / 3)
    assert independent == predicted
    assert independent[0] != independent[1]
    receipt = {
        'status': 'passed exact finite controls',
        'execution': {
            'python_executable': sys.executable,
            'python_version': platform.python_version(),
            'networkx_version': networkx.__version__,
            'dependency_install': 'python -m pip install --target /tmp/g4-whole-source-2110-deps networkx=='+networkx.__version__,
            'repository_root': str(ROOT),
            'command': 'PYTHONPATH=/tmp/g4-whole-source-2110-deps python research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/retained_core_gauge_check.py',
        },
        'scope': 'Admission, four full displayed profiles, one five-copy COMMON row, and one projected INDEPENDENT crossed cherry. The all-arity normalized identity is a separate hand proof.',
        'admission': admission,
        'profile_count': len(set(map(repr, profiles[0]))),
        'common_clades': sorted(''.join(sorted(c)) for c in common_clades),
        'independent_crossed_probabilities': list(map(str, independent)),
        'upstream_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                            for p in (UPSTREAM/'source_checks.py', UPSTREAM/'forest_algebra.py')},
    }
    out = Path(__file__).with_name('retained-core-gauge-check.json')
    out.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
