"""Narrow exact support checks for the one-coin partial-row compiler.

Author: Codex Work independent code-audit agent, /root/ind_protocol_code_audit.
Contribution: INDEPENDENT-CONTROL-20260930-1810Z.

Only two prescribed source-admitted two-switch gadget fixtures are tested.
All their global switches are enumerated as a small independent tree-edge
oracle. This is not a source-network census or a proof by testing.
"""
from __future__ import annotations

from fractions import Fraction as F
from itertools import combinations
from pathlib import Path
import importlib.util
import json
import sys

from control_protocol import (
    Edge, Network, cf, compile_row, contrast, sample_identifier_environment,
)


def load_file(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


HERE = Path(__file__).resolve().parent
MENU = load_file(
    'independent_audit_old_menu_checks',
    HERE.parent / '2026-09-30-control-menu-continuation' / 'menu_checks.py',
)
ORACLE = load_file('independent_audit_tree_edge_checks', HERE / 'checks.py')


def fixture(r, cherry_taxa):
    """Extend the admitted old gadget only by pendant labelled cherries.

    Original parent-bit order is preserved explicitly, including parallel arcs.
    Every edge has survival 1/2 and every natural edge-0 probability is 1/2.
    Pendant cherries preserve the old fixture's written outer-face admission.
    """
    base, hybrid = MENU.gadget(r)
    leaves = {t: t for t in 'ABCD' if t not in cherry_taxa}
    raw = []
    for parent, child in base:
        if child in cherry_taxa:
            stem = child + '_stem'
            raw.append((parent, stem))
            for label in (child + '0', child + '1'):
                raw.append((stem, label))
                leaves[label] = label
        else:
            raw.append((parent, child))
    ids = tuple(hybrid[i][0] for i in range(r))
    for i in range(r):
        h, options = hybrid[i]
        raw.extend((options[bit], h) for bit in (0, 1))
    network = Network(
        tuple(Edge(a, b, F(1, 2), f'g_e{k}') for k, (a, b) in enumerate(raw)),
        leaves,
        {h: F(1, 2) for h in ids},
    )
    network.structural_checks()
    return network, ids


class BitStub:
    def __init__(self, bit):
        self.bit = bit
        self.calls = []

    def randrange(self, n):
        self.calls.append(n)
        assert n == 2
        return self.bit


def runtime_environments(compiled, row):
    """Check the two equal-weight runtime outputs, without locus simulation."""
    environments = []
    for bit in (0, 1):
        rng = BitStub(bit)
        env = compiled.sample_two_configuration_environment(rng)
        assert rng.calls == ([2] if compiled.synchronize else [])
        assert all(env[h] == value for h, value in compiled.fixed.items())
        assert all(env[h] == bit for h in compiled.synchronize)
        assert set(env) == set(compiled.fixed) | set(compiled.synchronize)
        environments.append(env)

        graph_free_rng = BitStub(bit)
        graph_free = sample_identifier_environment(
            row, compiled.network.inheritance, graph_free_rng,
            two_configurations=True,
        )
        free = {h for h, value in row.items() if value is None}
        assert graph_free_rng.calls == ([2] if free else [])
        assert all(graph_free[h] == bit for h in free)
        assert all(graph_free[h] == value for h, value in compiled.fixed.items())
        assert all(graph_free[h] == env[h] for h in env)
    for h in compiled.synchronize:
        assert sum(F(1, 2) for env in environments if env[h] == 0) == F(1, 2)
    configurations = len({tuple(sorted(env.items())) for env in environments})
    assert configurations <= 2
    return environments, configurations


def check_fixture(r, cherry_taxa):
    network, ids = fixture(r, cherry_taxa)
    taxa = sorted(network.leaves.values())
    quartets = list(combinations(taxa, 4))
    # fixed={} enumerates all 2**r global switches only on these tiny fixtures.
    support = {q: ORACLE.tree_mixture(network, q, {})[1] for q in quartets}
    assert all(len(s) <= 2 for s in support.values())
    result = {
        **network.structural_checks(),
        'cherry_taxa': list(cherry_taxa),
        'original_hybrid_order': list(ids),
        'sample_descendant_copies': network.descendant_counts(),
        'global_switches': 2**r,
        'quartets': len(quartets),
        'switching_quartet_oracle_cases': (2**r) * len(quartets),
        'menus': [],
    }
    for name, values in (
        ('single_menu', MENU.single_menu(r)),
        ('partial_array', MENU.partial_array(r)),
    ):
        assert MENU.covers(values, r)
        maxima = {q: [F(0)] * 3 for q in quartets}
        law_differences = 0
        example = None
        configuration_counts = []
        for values_row in values:
            row = dict(zip(ids, values_row))
            compiled = compile_row(network, row)
            environments, config_count = runtime_environments(compiled, row)
            configuration_counts.append(config_count)
            for q in quartets:
                correlated = compiled.two_configuration_quartet_law(q)
                # Independent edge-cut calculations verify each of the two
                # conditional tree mixtures, independently of cf's recurrence.
                tree_laws = [ORACLE.tree_mixture(network, q, env)[0]
                             for env in environments]
                tree_average = tuple((tree_laws[0][j] + tree_laws[1][j]) / 2
                                     for j in range(3))
                assert correlated == tree_average
                assert all(type(x) is F and x >= 0 for x in correlated)
                assert sum(correlated) == 1
                residual = contrast(correlated)
                assert {j for j in range(3) if residual[j] > 0} <= support[q]
                maxima[q] = [max(maxima[q][j], residual[j]) for j in range(3)]
                common = cf(network, q, fixed=compiled.fixed, shared=ids)
                if correlated != common:
                    law_differences += 1
                    if example is None:
                        example = {
                            'quartet': list(q), 'row': row,
                            'correlated_cf': list(map(str, correlated)),
                            'product_common_cf': list(map(str, common)),
                        }
        for q in quartets:
            recovered = {j for j in range(3) if maxima[q][j] > 0}
            assert recovered == support[q], (r, name, q, recovered, support[q])
            assert all(maxima[q][j] >= F(1, 4) for j in support[q]), (
                r, name, q, maxima[q], support[q]
            )
        minimum = min(maxima[q][j] for q in quartets for j in support[q])
        result['menus'].append({
            'name': name, 'rows': len(values),
            'row_quartet_readouts': len(values) * len(quartets),
            'conditional_tree_oracle_checks': 2 * len(values) * len(quartets),
            'support_comparisons': len(quartets),
            'minimum_present_max_contrast': str(minimum),
            'claimed_finite_threshold': '1/4 (g=1/2, tau=ln(2))',
            'runtime_configuration_counts_by_row': configuration_counts,
            'runtime_coin_calls_per_row': [int(n == 2) for n in configuration_counts],
            'synchronized_site_marginal_edge_0_weight': '1/2',
            'differences_from_product_common_law': law_differences,
            'first_law_difference': example,
        })
    return result


def main():
    fixtures = [check_fixture(3, ('A', 'C')),
                check_fixture(4, ('A', 'C', 'B'))]
    menus = [menu for model in fixtures for menu in model['menus']]
    result = {
        'status': 'PASS',
        'contributor': 'Codex Work independent code-audit agent /root/ind_protocol_code_audit',
        'scope': 'two cherry-extended prescribed gadget fixtures; exact finite checks only',
        'fixtures': fixtures,
        'fixture_count': len(fixtures),
        'global_switches_across_fixtures': sum(x['global_switches'] for x in fixtures),
        'switching_quartet_oracle_cases': sum(x['switching_quartet_oracle_cases'] for x in fixtures),
        'correlated_row_quartet_readouts': sum(x['row_quartet_readouts'] for x in menus),
        'conditional_tree_oracle_checks': sum(x['conditional_tree_oracle_checks'] for x in menus),
        'menu_quartet_support_comparisons': sum(x['support_comparisons'] for x in menus),
        'differences_from_product_common_law': sum(x['differences_from_product_common_law'] for x in menus),
        'not_executed': [
            'broad source-network census', 'formal proof',
            'full joint gene-law enumeration', 'physical intervention',
        ],
        'source_admission': 'old gadget written proof + pendant cherry extension; degree/LSA/cut checks',
    }
    assert result['differences_from_product_common_law'] > 0
    path = HERE / 'correlated-checks.json'
    path.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'fixtures'}, indent=2))


if __name__ == '__main__':
    main()
