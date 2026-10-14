#!/usr/bin/env python3
"""Check a bounded unknown-registry search without inferring global NO."""
from pathlib import Path
import argparse
import hashlib
import json
from solver import digest, identity, InvalidInput
from bounded_search import candidate_request
from verify_certificate import verify_result, require


def verify_search(path, replay_backend=False):
    path = Path(path)
    result = json.loads(path.read_bytes())
    require(result['schema'] == 'bounded-incomplete-original-registry-YES-search-v1',
            'Wrong bounded-search schema.')
    require(result['request_sha256'] == digest(result['request']), 'Wrong original request digest.')
    require(result['upstream'] == identity(), 'Wrong upstream identity.')
    require(result['request']['registry']['complete'] is False, 'Original registry must be incomplete.')
    require(result['request'].get('task', 'find_source') == 'find_source', 'Unsupported unknown-size identification.')
    for claim in ('unknown_size_termination_or_global_NO_claimed',
                  'Lean_verification_claimed', 'empirical_admission_claimed'):
        require(result.get(claim) is False, 'Unsupported bounded-search promotion.')
    require(result['status'] in ('SAT_ADMITTED_SOURCE_UNKNOWN_SIZE_SEARCH',
                                'UNKNOWN_BOUNDED_SEARCH_EXHAUSTED', 'UNKNOWN_RESOURCE_LIMIT'),
            'Unknown registry search cannot certify terminal NO.')
    member_results = []
    for index, member in enumerate(result['members']):
        require(member['extra_hybrids'] == index, 'Nonconsecutive search registry.')
        relative = Path(member['result'])
        require(relative.as_posix() == f'extra-{index}/RESULT.json', 'Wrong local member path.')
        member_path = path.parent / relative
        require(hashlib.sha256(member_path.read_bytes()).hexdigest() == member['sha256'],
                'Changed member result bytes.')
        child = json.loads(member_path.read_bytes())
        expected = candidate_request(result['request'], index)
        # Resource budgets may decrease; the mathematical experiment is unchanged.
        expected.pop('limits', None)
        actual = dict(child['request'])
        actual.pop('limits', None)
        require(actual == expected and child['status'] == member['status'],
                'Candidate changed source controls, data, parameter ties or readout.')
        verify_result(member_path, replay_backend)
        member_results.append(child)
    if result['status'] == 'SAT_ADMITTED_SOURCE_UNKNOWN_SIZE_SEARCH':
        index = result['witness_member']
        require(type(index) is int and 0 <= index < len(member_results)
                and member_results[index]['status'] == 'SAT_ONE_COHERENT_ADMITTED_SOURCE',
                'No exact admitted positive source witness.')
    return {'status': 'PASS_BOUNDED_SEARCH_AND_MEMBER_CERTIFICATES',
            'registries_checked': len(member_results),
            'global_unknown_size_NO_inferred': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('result')
    parser.add_argument('--replay-backend', action='store_true')
    args = parser.parse_args()
    try:
        report = verify_search(args.result, args.replay_backend)
    except (InvalidInput, KeyError, TypeError, ValueError, OSError) as error:
        print(json.dumps({'status': 'FAIL_BOUNDED_SEARCH_CERTIFICATE', 'reason': str(error)}))
        return 1
    print(json.dumps(report))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
