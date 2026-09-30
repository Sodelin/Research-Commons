"""Explicit high-level positive sources, not a source-class census.

Start with consecutive paired tips of one rooted plane tree, then fold each
pair to a pendant hybrid. The chosen cherries cross the pair boundaries, so
every ordinary internal edge lies in the one reticulate blob. Optional hybrid
cherries give the independent-lineage pruning rule a multi-descendant test.
"""
from fractions import Fraction as F
import networkx as nx
from metric_partition_inverse import make_source


def ladder_source(level, hybrid_cherries=True):
    if level < 2:
        raise ValueError('Use level at least two for this fixture family')
    # Original cyclic leaf order: d,h1a,h1b,h2a,h2b,...,hra,hrb,c.
    # Consecutive cherries pair d with h1a, hib with h(i+1)a, hrb with c.
    # Folding consecutive equal-label tips gives the following explicit DAG.
    pairs = []
    for i in range(level + 1):
        left = 'd' if i == 0 else f'H{i}'
        right = 'c' if i == level else f'H{i+1}'
        pairs += [(f'C{i}', left), (f'C{i}', right)]
    # A rooted caterpillar joins C0,...,C_level in that order.
    for i in range(level):
        pairs += [(f'R{i}', f'C{i}'),
                  (f'R{i}', f'R{i+1}' if i < level - 1 else f'C{level}')]
    labels = ['c', 'd']
    for i in range(1, level + 1):
        if hybrid_cherries and i in (1, level):
            pairs += [(f'H{i}', f'A{i}'), (f'A{i}', f'x{i}a'), (f'A{i}', f'x{i}b')]
            labels += [f'x{i}a', f'x{i}b']
        else:
            pairs += [(f'H{i}', f'x{i}')]
            labels += [f'x{i}']
    graph = nx.DiGraph(pairs)
    ages = {}
    for v in reversed(list(nx.topological_sort(graph))):
        ages[v] = 0 if v in labels else 2 + max(ages[w] for w in graph.successors(v))
    gammas = {f'H{i}': F(1, 100000 + level) if i == level else F(1, 3)
              for i in range(1, level + 1)}
    source = make_source(f'single_blob_level_{level}_paired_tip_ladder', ages, pairs, labels, gammas)
    admission = source.validate()
    if admission['level'] != level or admission['reticulations'] != level:
        raise AssertionError((level, admission))
    return source


def stress_sources():
    return [ladder_source(k) for k in (3, 5, 8)]
