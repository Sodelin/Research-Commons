#!/usr/bin/env python3
"""Recompute actual source laws and check a delivered solver certificate.

Exact witness/linear checks and a fresh same-backend UNSAT replay have
different trust labels. Neither establishes Lean verification. Checks remain
enabled under Python -O; supplied SMT query hashes cannot replace rederiving
the actual source constraints.
"""
from pathlib import Path
import argparse
import hashlib
import json
from solver import (
    identity, digest, prepare_request, equations, verify_witness,
    verify_linear_certificate, Network, admitted, census, canonical_key,
    z3, Unsupported, InvalidInput, target_json, exact_backend_solver, physical_realization,
)


def require(condition, message):
    if not condition:
        raise InvalidInput(message)


def local_evidence_path(directory, name):
    require(isinstance(name, str) and Path(name).name == name,
            'Evidence must use a single local filename.')
    return directory / name


def verify_result(path, replay_backend=False):
    path = Path(path)
    result = json.loads(path.read_bytes())
    require(result['request_sha256'] == digest(result['request']),
            'Request digest mismatch.')
    require(result['upstream'] == identity(), 'Pinned upstream identity mismatch.')
    for claim in ('unknown_size_termination_or_global_NO_claimed',
                  'Lean_verification_claimed', 'empirical_admission_claimed'):
        require(result.get(claim) is False, 'Unsupported scope claim: ' + claim)

    if result['status'] in ('UNKNOWN_UNSUPPORTED_OR_UNADMITTED_CONTRACT',
                            'INVALID_INPUT'):
        try:
            prepare_request(result['request'])
        except (Unsupported, InvalidInput, KeyError, TypeError):
            require(not result['entries'], 'Admission rejection has source entries.')
            return {'status': 'PASS_HONEST_ADMISSION_REJECTION',
                    'source_feasibility_or_empirical_NO_inferred': False}
        raise InvalidInput('Rejection does not match current admission rules.')

    n, ids, modes, taxa, rows = prepare_request(result['request'])
    require(result['status'] in ('SAT_ONE_COHERENT_ADMITTED_SOURCE',
                                'UNSAT_COMPLETE_KNOWN_REGISTRY',
                                'AMBIGUOUS_TARGET_TWO_ADMITTED_SOURCE_WITNESSES',
                                'IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY',
                                'UNKNOWN_INCOMPLETE_DECISION',
                                'UNKNOWN_RESOURCE_LIMIT'), 'Unknown result status.')
    keys = []
    independent = 0
    replayed = 0
    for entry in result['entries']:
        graph = entry['graph']
        network = Network(tuple(tuple(edge) for edge in graph['edges']),
                          graph['root'], tuple(graph['leaves']))
        require(admitted(network), 'Delivered source fails actual source admission.')
        require(set(network.leaves) == {f'L{i}' for i in range(n)},
                'Wrong original taxon carrier.')
        require(set(network.structure()[3]) == {f'H{i}' for i in range(len(ids))},
                'Wrong complete original hybrid registry.')
        require(entry['mechanism'] in modes, 'Wrong inheritance mode.')
        eq, _ = equations(network, entry['mechanism'], rows)
        variables = list(network.parameters()[0]) + list(network.parameters()[1].values())
        require([str(value) for value in eq] == entry['equations'],
                'Delivered equations differ from the actual joint source compiler.')
        require(digest(entry['equations']) == entry['equation_sha256'],
                'Equation digest mismatch.')
        require(entry['target'] == json.loads(json.dumps(target_json(network))),
                'Displayed target differs from actual original switchings.')
        keys.append((canonical_key(network), entry['mechanism']))
        if entry['status'] == 'SAT_INDEPENDENT_EXACT_WITNESS':
            verify_witness(network, entry['mechanism'], rows, entry['values'])
            require(entry['physical_realization'] == physical_realization(network, entry['values']),
                    'Physical calendar/rate construction differs from the admitted source witness.')
            independent += 1
        elif entry['status'] == 'UNSAT_INDEPENDENT_EXACT_LINEAR_CERTIFICATE':
            require(verify_linear_certificate(eq, variables, entry['certificate']),
                    'Invalid exact rational contradiction certificate.')
            independent += 1
        elif entry['status'] == 'UNSAT_EXACT_BACKEND_PROOF_NOT_INDEPENDENTLY_CHECKED':
            query = local_evidence_path(path.parent, entry['query'])
            proof = local_evidence_path(path.parent, entry['proof'])
            require(hashlib.sha256(query.read_bytes()).hexdigest() == entry['query_sha256'],
                    'Query evidence hash mismatch.')
            require(hashlib.sha256(proof.read_bytes()).hexdigest() == entry['proof_sha256'],
                    'Backend proof evidence hash mismatch.')
            if replay_backend:
                # Rebuild from the inspected source, not from a user-supplied SMT file.
                check, _ = exact_backend_solver(eq, variables)
                require(check.check() == z3.unsat,
                        'Recomputed actual source problem is not certified UNSAT.')
                replayed += 1
        elif entry['status'] not in ('UNKNOWN_EXACT_BACKEND',
                                     'SAT_CANDIDATE_INDEPENDENT_CHECK_PENDING'):
            raise InvalidInput('Unexpected source entry status.')

    require(len(keys) == len(set(keys)), 'Duplicate original source/mode entry.')
    if result['status'] == 'SAT_ONE_COHERENT_ADMITTED_SOURCE':
        index = result['witness_entry']
        require(type(index) is int and 0 <= index < len(result['entries']),
                'Invalid witness entry index.')
        require(result['entries'][index]['status'] == 'SAT_INDEPENDENT_EXACT_WITNESS',
                'SAT has no independently checked exact source witness.')
    if result['status'] == 'AMBIGUOUS_TARGET_TWO_ADMITTED_SOURCE_WITNESSES':
        require(result['request'].get('task') == 'identify_target', 'Wrong identification task.')
        indices = result['witness_entries']
        require(isinstance(indices, list) and len(indices) == 2
                and all(type(index) is int and 0 <= index < len(result['entries'])
                        for index in indices), 'Invalid ambiguity witness indices.')
        witnesses = [result['entries'][index] for index in indices]
        require(all(entry['status'] == 'SAT_INDEPENDENT_EXACT_WITNESS'
                    for entry in witnesses), 'Ambiguity needs two exact source witnesses.')
        target_kind = result['request'].get('target_kind', 'nontrivial_displayed_split_union')
        require(result['target_kind'] == target_kind
                and witnesses[0]['target'][target_kind] != witnesses[1]['target'][target_kind],
                'The two admitted witnesses do not have different requested targets.')
    if result['catalogue_exhausted']:
        expected = {(canonical_key(net), mode)
                    for net in census(n, len(ids)) for mode in modes}
        require(set(keys) == expected, 'Incomplete supplied finite source catalogue.')
    if result['status'] == 'UNSAT_COMPLETE_KNOWN_REGISTRY':
        require(result['catalogue_exhausted'] is True
                and all(entry['status'].startswith('UNSAT')
                        for entry in result['entries']), 'Incomplete catalogue-NO.')
        if result['verification'] == 'INDEPENDENT_EXACT_LINEAR_CERTIFICATES':
            require(independent == len(keys), 'Missing independent linear certificates.')
        else:
            require(replay_backend and independent + replayed == len(keys),
                    'General backend UNSAT needs explicit fresh backend replay; '
                    'the same-backend trust label is retained.')
    if result['status'] == 'IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY':
        require(result['request'].get('task') == 'identify_target'
                and result['catalogue_exhausted'] is True, 'Identification needs complete search.')
        target_kind = result['request'].get('target_kind', 'nontrivial_displayed_split_union')
        require(result['target_kind'] == target_kind, 'Wrong target carrier.')
        satisfying = [entry for entry in result['entries']
                      if entry['status'] == 'SAT_INDEPENDENT_EXACT_WITNESS']
        require(satisfying and all(entry['target'][target_kind] == result['identified_target']
                                  for entry in satisfying), 'Incompatible satisfying targets.')
        require(all(entry['status'].startswith('UNSAT')
                    or entry['status'] == 'SAT_INDEPENDENT_EXACT_WITNESS'
                    for entry in result['entries']), 'Identification has unresolved source rows.')
        index = result['witness_entry']
        require(type(index) is int and 0 <= index < len(result['entries'])
                and result['entries'][index] in satisfying, 'Identification has no exact witness.')
        if result['verification'] == 'INDEPENDENT_EXACT_ALGEBRAIC_AND_LINEAR_CERTIFICATES':
            require(independent == len(keys), 'Missing exact source feasibility certificates.')
        else:
            require(replay_backend and independent + replayed == len(keys),
                    'Identification with backend exclusions needs explicit fresh replay.')
    return {'status': 'PASS_SOURCE_AND_CERTIFICATE_RECOMPUTATION',
            'entries': len(keys), 'independent_exact_entries': independent,
            'same_backend_unsat_replays': replayed,
            'global_unknown_size_NO_inferred': False,
            'Lean_verification_inferred': False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('result')
    parser.add_argument('--replay-backend', action='store_true')
    args = parser.parse_args()
    try:
        report = verify_result(args.result, args.replay_backend)
    except (InvalidInput, KeyError, TypeError, ValueError, OSError) as error:
        print(json.dumps({'status': 'FAIL_CERTIFICATE', 'reason': str(error)}))
        return 1
    print(json.dumps(report))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
