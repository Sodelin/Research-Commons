"""Exact finite controls for an uncalibrated crossed-cherry inequality candidate.

Uses the inherited finite original-source compiler, with full topology output
and selected-label pruning. This finite check is not an all-source proof.
"""
from pathlib import Path
from fractions import Fraction as Q
from dataclasses import replace
import sys, json, hashlib
ROOT = Path(__file__).resolve().parents[3]
UPSTREAM = ROOT / 'research/2026-10-01-g4-admitted-testers-0819z'
sys.path.insert(0, str(UPSTREAM))
from source_checks import root_two_hybrids, balanced, insert_chain, compile_source
from forest_algebra import leaves

def prune(t, keep):
    if isinstance(t, int):
        return t if t in keep else None
    a, b = (prune(s, keep) for s in t)
    if a is None: return b
    if b is None: return a
    return (a, b)

def crossed(law, a1, a2, b):
    out = Q(0)
    for t, p in law.items():
        s = prune(t, {a1, a2, b})
        if any(set(leaves(c)) == {a1, b} for c in s):
            out += p
    return out

def check(source, name):
    rows = []
    for a in 'abcd':
        allocation = {x: 2 if x == a else 1 for x in 'abcd'}
        labels, at = {}, 0
        for x in sorted(allocation):
            labels[x] = tuple(range(at, at+allocation[x])); at += allocation[x]
        lc = compile_source(source, allocation, 'common')
        li = compile_source(source, allocation, 'independent')
        graph = source.graph()
        import networkx as nx
        for b in 'abcd':
            if a == b: continue
            c = crossed(lc, *labels[a], labels[b][0])
            u = crossed(li, *labels[a], labels[b][0])
            exclusive = any(nx.has_path(graph, h, a) and not nx.has_path(graph, h, b)
                            for h in source.gamma)
            assert u >= c
            assert (u > c) == exclusive
            rows.append({'a': a, 'b': b, 'common': str(c), 'independent': str(u),
                         'difference': str(u-c), 'exclusive_hybrid': exclusive})
    return {'fixture': name, 'source_admission': source.validate(), 'ordered_pairs': rows}

def main():
    base = root_two_hybrids()
    varied = replace(base,
        edges=tuple(replace(e, x=Q((i*3)%7+1, (i*3)%7+3)) for i,e in enumerate(base.edges)),
        gamma={'H0':Q(1,4), 'H1':Q(4,7)})
    # Unequal private cells below the nontrivial two-hybrid meeting blob.
    mixed = insert_chain(base, 'a', Q(2,3), ((Q(1,5),Q(4,5),Q(2,7),Q(3,4)),))
    sources = [(balanced(), 'ordinary-tree-zero-gap'),
               (base, 'two-hybrid-root'), (varied, 'two-hybrid-root-varied'),
               (mixed, 'two-hybrid-root-plus-unequal-private-cell')]
    results = [check(s, name) for s,name in sources]
    result = {'status':'all exact finite controls passed', 'fixtures':len(results),
              'ordered_pair_comparisons':sum(len(x['ordered_pairs']) for x in results),
              'arithmetic':'fractions.Fraction',
              'scope':'Finite source controls only; no general theorem or Lean verification.',
              'upstream_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in (UPSTREAM/'source_checks.py', UPSTREAM/'forest_algebra.py')},
              'results':results}
    output = Path(__file__).with_name('uncalibrated-pair-results.json')
    output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='results'}, indent=2))

if __name__ == '__main__': main()
