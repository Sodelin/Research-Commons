#!/usr/bin/env python3
"""Resource-bounded YES search when the original hybrid registry is incomplete.

Each candidate has one complete finite original registry. Exhausting finitely
many candidate registries is UNKNOWN for the unbounded original source class.
"""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import time
from solver import identity, digest, prepare_request, solve, InvalidInput, Unsupported


def candidate_request(request, extra):
    candidate = copy.deepcopy(request)
    ids = list(candidate['registry']['hybrid_ids'])
    names = []
    for number in range(extra):
        name = f'candidate_unmarked_{number}'
        while name in ids or name in names:
            name = '_' + name
        names.append(name)
    candidate['registry'] = {'complete': True, 'hybrid_ids': ids + names}
    return candidate


def search(request, outdir, max_extra):
    outdir = Path(outdir)
    outdir.mkdir(parents=True, exist_ok=True)
    if type(max_extra) is not int or max_extra < 0:
        raise InvalidInput('max-extra-hybrids must be a nonnegative integer.')
    if not isinstance(request, dict) or not isinstance(request.get('registry'), dict):
        raise InvalidInput('A finite declared accessible registry is required.')
    if request['registry'].get('complete') is not False:
        raise InvalidInput('Use solver.py for a declared complete original registry.')
    if request.get('task', 'find_source') != 'find_source':
        raise Unsupported('A bounded incomplete-registry search cannot establish unique target identification.')
    # This also rejects forcing IDs not in the declared accessible registry.
    prepare_request(candidate_request(request, 0))
    start = time.monotonic()
    seconds = request.get('limits', {}).get('seconds', 120)
    maximum = request.get('limits', {}).get('max_sources', 10000)
    members = []
    examined = 0
    base = {'schema': 'bounded-incomplete-original-registry-YES-search-v1',
            'request': request, 'request_sha256': digest(request),
            'max_extra_hybrids_searched': max_extra,
            'upstream': identity(), 'members': members,
            'unknown_size_termination_or_global_NO_claimed': False,
            'Lean_verification_claimed': False, 'empirical_admission_claimed': False}
    for extra in range(max_extra + 1):
        remaining = seconds - (time.monotonic() - start)
        if remaining <= 0 or examined >= maximum:
            return {**base, 'status': 'UNKNOWN_RESOURCE_LIMIT',
                    'source_count_examined': examined}
        candidate = candidate_request(request, extra)
        candidate.setdefault('limits', {}).update(seconds=remaining,
                                                  max_sources=maximum-examined)
        folder = outdir / f'extra-{extra}'
        result = solve(candidate, folder)
        path = folder / 'RESULT.json'
        path.write_text(json.dumps(result, indent=2) + '\n')
        members.append({'extra_hybrids': extra, 'result': path.relative_to(outdir).as_posix(),
                        'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                        'status': result['status']})
        examined += result.get('source_count_examined', 0)
        if result['status'] == 'SAT_ONE_COHERENT_ADMITTED_SOURCE':
            return {**base, 'status': 'SAT_ADMITTED_SOURCE_UNKNOWN_SIZE_SEARCH',
                    'witness_member': len(members)-1,
                    'source_count_examined': examined,
                    'verification': 'EXACT_ONE_SOURCE_WITNESS_RECOMPUTABLE',
                    'scope': 'positive witness in the unbounded source class; no negative stopping claim'}
        if result['status'] == 'UNKNOWN_RESOURCE_LIMIT':
            return {**base, 'status': 'UNKNOWN_RESOURCE_LIMIT',
                    'source_count_examined': examined}
    return {**base, 'status': 'UNKNOWN_BOUNDED_SEARCH_EXHAUSTED',
            'source_count_examined': examined,
            'scope': 'No certified witness found in finite attempted registries; '
                     'larger or unresolved admitted sources remain possible.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request')
    parser.add_argument('--output', required=True)
    parser.add_argument('--max-extra-hybrids', required=True, type=int)
    args = parser.parse_args()
    try:
        request = json.loads(Path(args.request).read_bytes())
        result = search(request, args.output, args.max_extra_hybrids)
    except (InvalidInput, Unsupported, KeyError, TypeError, ValueError) as error:
        print(json.dumps({'status': 'REJECTED_SEARCH_REQUEST', 'reason': str(error)}))
        return 2
    (Path(args.output) / 'SEARCH-RESULT.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({key: result[key] for key in ('status', 'source_count_examined', 'scope')
                      if key in result}, indent=2))
    return 0 if result['status'] == 'SAT_ADMITTED_SOURCE_UNKNOWN_SIZE_SEARCH' else 2


if __name__ == '__main__':
    raise SystemExit(main())
