#!/usr/bin/env python3
"""Compile actual finite original sources into the accepted G7 RCF predicate.

This exports a complete actual-source design problem when enumeration finishes.
A backend decision or an executable CAD policy is a further evidence stage.
"""
from pathlib import Path
import argparse
import hashlib
import json
import signal
import time
import sympy as sp
from sympy.printing.mathematica import mathematica_code
from solver import (
    ROOT, identity, digest, compile_law, readout_law, census, admitted,
    target_json, graph_json, InvalidInput, Unsupported, TimeLimit,
)


def validated(request):
    if not isinstance(request, dict) or request.get('registry', {}).get('complete') is not True:
        raise Unsupported('Exact G7 design needs a COMPLETE finite original registry.')
    if set(request) - {'n', 'registry', 'mechanisms', 'samples', 'readout', 'target_kind',
                       'deterministic_rows', 'supports', 'budgets', 'clock_contract',
                       'resource_contract', 'limits'}:
        raise Unsupported('Unsupported design constraints need their actual semialgebraic encoder; they cannot be ignored.')
    if set(request['registry']) - {'complete', 'hybrid_ids'}:
        raise Unsupported('Unsupported original-registry constraints.')
    n = request.get('n')
    if type(n) is not int or n < 2:
        raise InvalidInput('n must be an integer at least2.')
    ids = request['registry'].get('hybrid_ids', [])
    if not isinstance(ids, list) or any(not isinstance(v, str) for v in ids) or len(set(ids)) != len(ids):
        raise InvalidInput('Original hybrid IDs must be distinct strings.')
    modes = request.get('mechanisms', ['common', 'independent'])
    if not isinstance(modes, list) or not modes or any(v not in ('common', 'independent') for v in modes) or len(set(modes)) != len(modes):
        raise InvalidInput('Specify a finite nonempty inheritance-mode set.')
    samples = request.get('samples', {f'L{i}': [f'L{i}'] for i in range(n)})
    if not isinstance(samples, dict) or not set(samples) <= {f'L{i}' for i in range(n)} or any(not isinstance(v, list) for v in samples.values()):
        raise InvalidInput('Samples must attach finite copy-label lists to original taxa L0,... .')
    labels = sum(samples.values(), [])
    if not labels or any(not isinstance(v, str) for v in labels) or len(set(labels)) != len(labels):
        raise InvalidInput('Copy labels must be unique and the total panel nonempty.')
    kind = request.get('readout', 'unrooted_splits')
    if kind not in ('rooted', 'unrooted_splits'):
        raise Unsupported('The pooled design exporter uses one common rooted or unrooted readout; differently labelled or DNA/calendar menus need their own exact affine encoder.')
    target = request.get('target_kind', 'nontrivial_displayed_split_union')
    if target not in ('nontrivial_displayed_split_union', 'whole_switching_split_systems'):
        raise Unsupported('Use a declared actual switching target.')
    operations = request.get('deterministic_rows')
    if not isinstance(operations, list) or not operations:
        raise InvalidInput('Supply a finite nonempty deterministic original-ID row menu.')
    forces = []
    for operation in operations:
        if not isinstance(operation, dict) or not set(operation) <= set(ids) or any(type(v) is not int or v not in (0, 1) for v in operation.values()):
            raise InvalidInput('Each deterministic row addresses original IDs and incoming bits0/1.')
        forces.append({f'H{ids.index(h)}': bit for h, bit in operation.items()})
    if len({digest(v) for v in operations}) != len(operations):
        raise InvalidInput('Duplicate deterministic row menu.')
    supports = request.get('supports', [[i+1] for i in range(len(forces))])
    if not isinstance(supports, list) or not supports or any(not isinstance(v, list) or not v or any(type(i) is not int or not 1 <= i <= len(forces) for i in v) or len(set(v)) != len(v) for v in supports):
        raise InvalidInput('Supports are finite nonempty lists of distinct1-based menu indices.')
    budgets = request.get('budgets')
    if not isinstance(budgets, list) or not budgets or any(not isinstance(b, list) or len(b) != 3 or any(type(v) is not int or v < 0 for v in b) for b in budgets):
        raise InvalidInput('Budgets are triples[programs,configurations,original-sites].')
    if request.get('clock_contract', 'free_positive_edge_specific') != 'free_positive_edge_specific':
        raise Unsupported('Extra clock/rate ties require an actual law model.')
    if request.get('resource_contract', 'reset_deletion_closed_path') != 'reset_deletion_closed_path':
        raise Unsupported('This G7 predicate needs reset/deletion-closed discrete PATH budgets.')
    limits = request.get('limits', {})
    if not isinstance(limits, dict) or type(limits.get('max_sources', 10000)) is not int or limits.get('max_sources', 10000) < 1:
        raise InvalidInput('A positive integer source limit is required.')
    if set(limits) - {'max_sources', 'seconds'}:
        raise Unsupported('Unsupported design resource limits.')
    seconds = limits.get('seconds', 120)
    if type(seconds) not in (float, int) or not 0 < seconds <= 86400:
        raise InvalidInput('Positive seconds<=86400 required.')
    return n, ids, modes, samples, kind, target, forces, supports, budgets, limits


def wl_list(values):
    return '{' + ','.join(map(str, values)) + '}'


def export(request, directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    up = identity()
    n, ids, modes, samples, kind, target, forces, supports, budgets, limits = validated(request)
    start = time.monotonic()
    records = []
    coordinates = set()
    count = 0
    def expired(*_):
        raise TimeLimit()
    old_handler = signal.signal(signal.SIGALRM, expired)
    signal.setitimer(signal.ITIMER_REAL, float(limits.get('seconds', 120)))
    try:
        for source in census(n, len(ids)):
            if count >= limits.get('max_sources', 10000):
                raise TimeLimit()
            count += 1
            if not admitted(source):
                raise InvalidInput('Nonadmitted census output.')
            for mode in modes:
                rows = [readout_law(compile_law(source, mode, forced=forcing, samples=samples), kind, [])
                        for forcing in forces]
                coordinates.update(event for row in rows for event in row)
                records.append((source, mode, rows, target_json(source)[target]))
    except TimeLimit:
        report = {'status': 'UNKNOWN_INCOMPLETE_ACTUAL_SOURCE_EXPORT', 'request': request,
                  'source_count_examined': count, 'catalogue_exhausted': False,
                  'source_policy_or_budget_verdict_claimed': False}
        (directory / 'EXPORT-RESULT.json').write_text(json.dumps(report, indent=2)+'\n')
        return report
    finally:
        signal.setitimer(signal.ITIMER_REAL, 0)
        signal.signal(signal.SIGALRM, old_handler)
    coordinates = sorted(coordinates, key=repr)
    target_codes = {}
    models = []
    wl_models = []
    for source, mode, rows, actual_target in records:
        key = digest(actual_target)
        code = target_codes.setdefault(key, len(target_codes))
        xs, gs = source.parameters()
        variables = list(xs) + list(gs.values())
        renamed = {symbol: sp.Symbol(f'theta{i}') for i, symbol in enumerate(variables)}
        laws = [[sp.expand(row.get(event, 0)).xreplace(renamed) for event in coordinates] for row in rows]
        domain = ' && '.join(f'0<theta{i}<1' for i in range(len(variables)))
        model = {'source': graph_json(source), 'mechanism': mode,
                 'variable_mapping': {str(k): str(v) for k, v in renamed.items()},
                 'domain': domain, 'laws': [[str(p) for p in row] for row in laws],
                 'target_code': code, 'actual_target': actual_target}
        models.append(model)
        wl_laws = '{' + ','.join('{' + ','.join(mathematica_code(value) for value in row) + '}' for row in laws) + '}'
        wl_models.append('<|"Vars"->' + wl_list(renamed.values()) + ',"Domain"->(' + domain + '),"Laws"->' + wl_laws + ',"Target"->' + str(code) + '|>')
    row_sites = [[ids.index(h)+1 for h in operation] for operation in request['deterministic_rows']]
    report = {'schema': 'complete-actual-original-source-G7-design-export-v1',
              'status': 'COMPLETE_ACTUAL_SOURCE_MODELS_EXPORTED_BACKEND_PENDING',
              'request': request, 'request_sha256': digest(request), 'upstream': up,
              'source_count_examined': count, 'source_mode_model_count': len(models),
              'catalogue_exhausted': True, 'joint_readout_coordinates': coordinates,
              'target_kind': target, 'models': models,
              'policy_extracted': False, 'budget_decided': False,
              'unknown_size_termination_or_global_NO_claimed': False,
              'Lean_verification_claimed': False, 'empirical_admission_claimed': False}
    (directory / 'ACTUAL-SOURCE-MODELS.json').write_text(json.dumps(report, indent=2)+'\n')
    code = (ROOT / 'continuous_optimizer_normalized.wl').read_text()
    code += '\nmodels={' + ',\n'.join(wl_models) + '};\n'
    code += 'supports=' + '{' + ','.join(wl_list(v) for v in supports) + '};\n'
    code += 'rowSites=' + '{' + ','.join(wl_list(v) for v in row_sites) + '};\n'
    code += 'budgets=' + '{' + ','.join(wl_list(v) for v in budgets) + '};\n'
    code += 'results=Table[{b,TimeConstrained[G7Decide[models,supports,b[[1]],rowSites,b[[2]],b[[3]]],45,"UNKNOWN_TIMEOUT"]},{b,budgets}];\n'
    code += '<|"Status"->"ACTUAL_SOURCE_BUDGET_DECISION", "ModelCount"->Length[models],"BudgetResults"->results,"PolicyExtracted"->False|>\n'
    path = directory / 'actual-source-design.wl'
    path.write_text(code)
    report = {key: report[key] for key in ('schema', 'status', 'request_sha256', 'source_count_examined', 'source_mode_model_count', 'catalogue_exhausted', 'policy_extracted', 'budget_decided')}
    report.update(wolfram_code_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  constructor_sha256=hashlib.sha256((ROOT / 'continuous_optimizer_normalized.wl').read_bytes()).hexdigest(),
                  source_models_sha256=hashlib.sha256((directory / 'ACTUAL-SOURCE-MODELS.json').read_bytes()).hexdigest(),
                  elapsed_seconds=time.monotonic()-start)
    (directory / 'EXPORT-RESULT.json').write_text(json.dumps(report, indent=2)+'\n')
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request')
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    try:
        result = export(json.loads(Path(args.request).read_bytes()), args.output)
    except (InvalidInput, Unsupported, KeyError, TypeError, ValueError) as error:
        print(json.dumps({'status': 'REJECTED_DESIGN_REQUEST', 'reason': str(error)}))
        return 2
    print(json.dumps(result, indent=2))
    return 0 if result['catalogue_exhausted'] else 2


if __name__ == '__main__':
    raise SystemExit(main())
