#!/usr/bin/env python3
"""Independent mathematical and provenance controls; no production changes."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction
import argparse
import hashlib
import importlib.util
import json
from math import comb
from pathlib import Path
import shutil
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
APP = ROOT / 'applications/practical-solver'


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--python-executable', required=True)
    args = parser.parse_args()
    paths = [APP / 'certified_bounds.py', APP / 'forest_baseline.py']
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    bounded = load('reviewer_bounded', paths[0])
    graph = load('reviewer_graph', paths[1])
    scratch = Path(tempfile.mkdtemp(prefix='validation-adversarial-', dir='/workspace/scratch'))
    checks = []

    def require(condition, label):
        checks.append({'label': label, 'passed': bool(condition)})
        if not condition:
            raise AssertionError(label)

    # Independent recurrence for the pure-death chain, rather than another copy
    # of the implementation's spectral formula or the inherited explicit engine.
    recurrence_cases = 0
    for m in range(1, 31):
        polynomials = {r: dict(graph.count_polynomial(m, r)) for r in range(1, m + 1)}
        total = {}
        for r, polynomial in polynomials.items():
            nxt = polynomials.get(r + 1, {})
            exponents = set(polynomial) | set(nxt)
            require(all(e * polynomial.get(e, 0) == comb(r, 2) * polynomial.get(e, 0)
                        - comb(r + 1, 2) * nxt.get(e, 0) for e in exponents),
                    f'count ODE m={m}, r={r}')
            require(sum(polynomial.values()) == int(r == m), f'initial count law m={m}, r={r}')
            for exponent, coefficient in polynomial.items():
                total[exponent] = total.get(exponent, 0) + coefficient
            recurrence_cases += 1
        require(all(v == int(e == 0) for e, v in total.items()), f'count normalization m={m}')
    g3 = graph.ForestGraph(3)
    for x in [Fraction(1, 101), Fraction(1, 2), Fraction(100, 101)]:
        require(g3.probability(((1, 2), 3), x) == (x - x**3) / 2, 'independent 3-leaf partial forest formula')
        require(g3.probability((((1, 2), 3),), x) == (1 - Fraction(3, 2)*x + x**3/2)/3,
                'independent 3-leaf complete tree formula')
    g2 = graph.ForestGraph(2)
    accepted_codes = []
    for code in range(g2.code_count):
        try:
            accepted_codes.append((code, g2.decode(code)))
        except ValueError:
            pass
    require(accepted_codes == sorted([(g2.encode((1, 2)), (1, 2)), (g2.encode(((1, 2),)), ((1, 2),))]),
            'every 18-bit two-leaf string has exactly two valid canonical encodings')

    # Exact arithmetic is checked without trusting the module's ceiling boolean.
    for b, eps, sig, M in [('1/2', '1/10', '1', '0'), ('1/999999', '1/999', '2/997', '100000'),
                           ('999/1000', '100', '100', '0'), ('1/3', '1/7', '9/11', '5/13')]:
        result = bounded.independent_count(b, eps, sig, M)
        delta = min(Fraction(eps), Fraction(sig)/(2*(Fraction(M)+1)))
        value = 2*(1+delta)/(Fraction(b)*delta)
        count = result['cell_count_bound']
        require(Fraction(result['delta']) == delta and count - 1 < value <= count,
                'independently recomputed rational bound and ceiling')
        require(result['provider_verified'] is False and result['source_count_bound_verified'] is False,
                'numeric count does not activate a provider')

    template = json.loads((APP/'examples/certified-bounds/conditional-count-unknown.json').read_text())
    result = bounded.consume(template, scratch/'conditional')
    require(result['status'] == 'UNKNOWN' and result['solver_called'] is False
            and result['bound_applied_to_catalogue'] is False, 'absent actual provider remains UNKNOWN')
    mutations = []
    def mutation(label, change):
        request = deepcopy(template); change(request); mutations.append((label, request))
    mutation('provider boolean is rejected', lambda q: q['count_certificate'].__setitem__('provider_evidence', True))
    mutation('positive endpoint is rejected', lambda q: q['count_certificate']['slots'][0].__setitem__('endpoint_score', '1/1000000'))
    mutation('approximate endpoint is rejected', lambda q: q['count_certificate']['slots'][0].__setitem__('endpoint_score', 0.0))
    mutation('COMMON substitution is rejected', lambda q: q['count_certificate'].__setitem__('mode', 'COMMON'))
    mutation('duplicate physical slots are rejected', lambda q: q['count_certificate']['slots'].append(deepcopy(q['count_certificate']['slots'][0])))
    mutation('unobserved floor is rejected', lambda q: q['count_certificate']['slots'][0]['survival_floor_evidence'].__setitem__('row_indices', []))
    mutation('changed complete row hash is rejected', lambda q: q['source_request']['rows'].append(deepcopy(q['source_request']['rows'][0])))
    mutation('slot count cannot become census budget', lambda q: q.__setitem__('max_extra_hybrids', 1))
    for index, (label, request) in enumerate(mutations):
        result = bounded.consume(request, scratch/f'negative-{index}')
        require(result['status'] == 'REFUSED_REQUEST' and result['source_feasibility_certified'] is False,
                label)
    both = deepcopy(template); both['count_certificate']['mode'] = 'BOTH'
    result = bounded.consume(both, scratch/'both')
    require(result['status'] == 'UNKNOWN' and 'UNKNOWN_BOTH_MENU_COMPILER_UNAVAILABLE' in result['integration_blockers'],
            'BOTH compiler absence is explicit')

    # Inject a genuinely checked result from a different complete request. The
    # injected producer receipt is a test fault; the source witness and semantic
    # checker are the real pinned backend, never a mock theorem/backend verdict.
    witness = json.loads((APP/'examples/certified-bounds/finite-witness.json').read_text())
    contradiction = json.loads((APP/'examples/certified-bounds/shared-row-exclusion.json').read_text())
    good = bounded.consume(witness, scratch/'good', args.python_executable)
    require(good['status'] == 'CERTIFIED_SOURCE_WITNESS', 'real original backend witness setup')
    actual_execute = bounded._execute
    def inject(command, workdir, name):
        if name == 'solver':
            for item in (scratch/'good/backend').iterdir():
                if item.is_file():
                    shutil.copyfile(item, Path(workdir)/'backend'/item.name)
            return {'command': list(map(str, command)), 'invoked': True, 'timeout': False, 'returncode': 0,
                    'test_fault': 'genuine cross-request artifact substitution'}
        return actual_execute(command, workdir, name)
    bounded._execute = inject
    try:
        result = bounded.consume(contradiction, scratch/'substituted', args.python_executable)
    finally:
        bounded._execute = actual_execute
    require(result['status'] in ('REFUSED_REQUEST', 'UNKNOWN') and result['source_feasibility_certified'] is False,
            'certified row-dropped producer artifact cannot certify requested two-row source')
    require(result.get('backend_result', {}).get('request') != contradiction['source_request'],
            'cross-request fault actually exercised')
    require(all(hashes[str(p.relative_to(ROOT))] == hashlib.sha256(p.read_bytes()).hexdigest() for p in paths),
            'reviewed production bytes unchanged during run')
    print(json.dumps({'status': 'PASS', 'reviewer': 'Codex independent validation lane', 'evidence_tier': 'INDEPENDENT_EXECUTION',
                      'source_hashes': hashes, 'scratch_directory': str(scratch), 'checks': checks,
                      'checks_run': len(checks), 'pure_death_recurrence_cases': recurrence_cases,
                      'exhaustive_encoding_bits': 18,
                      'limitations': 'Finite adversarial controls and exact finite arithmetic; no source-provider production, general G3/G4 proof, quantum circuit or Lean claim.'}, indent=2))
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
