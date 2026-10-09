#!/usr/bin/env python3
"""Exact recount of pinned saved evidence; does not execute a scientific solver."""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
BASE = 'research/2026-10-08-codex-integration-0825z/practical/'
PHYSICAL = ('h', 'u', 'v', 'rA', 'rB', 'rC', 'rAB', 'rR', 'g')
FEATURES = ('AC1', 'AC2', 'CC1', 'BC1', 'BC2', 'AB1', 'AB2', 'AA1', 'BB1')

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def require(condition, message):
    if not condition:
        raise ValueError(message)

def audit():
    manifest_raw = (HERE / 'SOURCE-EVIDENCE.json').read_bytes()
    manifest = json.loads(manifest_raw)
    captured = {}
    for row in manifest['saved_evidence'] + manifest['source_symbols']:
        path = ROOT / row['path']
        require(not path.is_symlink(), 'Symlink: ' + row['path'])
        raw = path.read_bytes()
        require(sha(raw) == row['sha256'] and len(raw) == row['bytes'],
                'Pinned identity mismatch: ' + row['path'])
        captured[row['path']] = raw
    def saved(path):
        return json.loads(captured[path])
    outputs = {}
    for name in ('original-multistage', 'finite-data'):
        result = saved(BASE + name + '/RESULT.json')
        request = saved(BASE + name + '/REQUEST.json')
        checker = result['checker']
        require(checker['details']['complete_numeric_replay'] is True,
                name + ': saved checker did not finish numerical replay')
        cover = checker['physical_cover']
        require(bool(cover), name + ': empty cover cannot certify width')
        widths = {}
        for k in PHYSICAL:
            low = min(F(c['box'][k][0]) for c in cover)
            high = max(F(c['box'][k][1]) for c in cover)
            span = F(request['box'][k][1]) - F(request['box'][k][0])
            width = high - low
            target = F(request['normalized_width_targets'][k])
            advertised = checker['widths'][k]
            require(F(advertised['width']) == width, name + ': width ' + k)
            require(F(advertised['normalized_ratio']) == width / span,
                    name + ': normalized width ' + k)
            require(advertised['met'] == (width <= span * target),
                    name + ': width decision ' + k)
            widths[k] = str(width / span)
        for flag in ('source_feasibility_certified', 'statistical_coverage_verified',
                     'parameter_accuracy_released'):
            require(checker[flag] is False, name + ': unexpected scientific promotion')
        met = all(F(widths[k]) <= F(request['normalized_width_targets'][k])
                  for k in PHYSICAL)
        require(checker['whole_union_width_target_met'] == met,
                name + ': inconsistent whole-union status')
        outputs[name] = {'evidence_tier': 'STATIC_EXACT_RECOUNT_OF_SAVED_RECEIPT',
                         'status': checker['status'], 'cells': len(cover),
                         'normalized_whole_union_widths': widths,
                         'maximum': str(max(map(F, widths.values())))}
    maximum = F(outputs['original-multistage']['maximum'])
    require(maximum == F(17394377843899475, 4611686018427387904),
            'Inherited arithmetic maximum changed')
    require(all(F(w) == 1 for w in outputs['finite-data']['normalized_whole_union_widths'].values()),
            'Archived finite-data widths changed')

    archive_path = 'research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json'
    archive = saved(archive_path)
    request = saved(BASE + 'finite-data/REQUEST.json')
    points = archive['source_parameter_points']
    means = archive['source_forward_mean_boxes']
    require(len(points) == len(means) == 2, 'Expected two source witnesses')
    for point, mean in zip(points, means):
        require(set(point) == set(PHYSICAL) and set(mean) == set(FEATURES),
                'Source witness schema changed')
        for k in PHYSICAL:
            low, high = map(F, point[k]); dl, dh = map(F, request['box'][k])
            require(dl <= low == high <= dh, 'Point outside original D: ' + k)
        for k in FEATURES:
            low, high = map(F, mean[k]); bl, bh = map(F, request['features'][k])
            require(bl <= low <= high <= bh, 'Mean enclosure outside actual band: ' + k)
    separation = abs(F(points[0]['rA'][0]) - F(points[1]['rA'][0])) / (F(6) - F(1, 2))
    require(separation == F(3, 55) and separation > F(1, 20),
            'Pair width obstruction changed')
    differential = saved(BASE + 'signed-differential/RESULT.json')
    cases = differential['cases']
    require(len(cases) == 39, 'Signed baseline count changed')
    require(all(c['matches'] is True and c['native'] == c['python_projection'] for c in cases),
            'Saved signed native/reference disagreement')
    completed = sum(c['native']['refusal'] is None for c in cases)
    require(completed == 13, 'Saved signed completion count changed')
    inventory = saved('research/2026-10-08-codex-integration-0825z/lean-release/terminal-37749239915/complete-environment-inventory.json')
    rows = {row['name']: row for row in inventory['declarations']}
    formal = []
    for item in manifest['lean_checked_providers']:
        row = rows.get(item['symbol'])
        require(row is not None and row['module'] == item['module'],
                'Formal provider missing from accepted selected inventory: ' + item['symbol'])
        require(not set(row['axioms']) - {'propext', 'Classical.choice', 'Quot.sound'},
                'Nonstandard formal provider axioms')
        formal.append({'symbol': item['symbol'], 'module': row['module'],
                       'evidence_tier': 'STATIC_MEMBERSHIP_IN_INHERITED_LEAN_CHECKED_INVENTORY'})
    return {'schema': 'practical_release_contract_audit_v1',
            'status': 'PASS', 'author': 'Codex contracts role; independent review separate',
            'executed_utc': datetime.now(timezone.utc).isoformat(),
            'audit_source_sha256': sha(Path(__file__).read_bytes()),
            'manifest_sha256': sha(manifest_raw),
            'scope': 'Exact saved-evidence recount and source/inventory identity; no producer/checker/native/Lean execution',
            'whole_application_lean_verified': False, 'scientific_confidence_admitted': False,
            'results': outputs,
            'pair_obstruction': {'points': 2, 'point_and_mean_enclosure_containment': True,
                                 'normalized_rA_separation': str(separation),
                                 'target': '1/20', 'scope': 'same archived bands and original source family'},
            'signed_saved_receipt': {'matched': len(cases), 'completed': completed,
                                    'refusals': len(cases)-completed},
            'accepted_formal_provider_membership': formal,
            'new_lean_draft_status': 'UNCHECKED_NO_COMPILER_LAUNCHED'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    result = audit()
    raw = (json.dumps(result, indent=2, sort_keys=True) + '\n').encode()
    if args.output:
        with args.output.open('xb') as out:
            out.write(raw)
    print(raw.decode(), end='')

if __name__ == '__main__':
    main()
