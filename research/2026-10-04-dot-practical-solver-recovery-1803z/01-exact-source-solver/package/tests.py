#!/usr/bin/env python3
"""End-to-end source/certificate, admission, dependence and tamper controls."""
from pathlib import Path
import copy
import hashlib
import json
import subprocess
import sys
import time
import sympy as sp
import networkx as nx
import solver as s
from verify_certificate import verify_result, require
from verify_search import verify_search
from passive_quartet_policy import execute
from export_design import export
from tree_design_reduction import reduce_design

ROOT = Path(__file__).resolve().parent


def run_case(name, expected):
    request_path = ROOT/'examples'/f'{name}.json'
    folder = ROOT/'runs'/name
    process = subprocess.run([sys.executable, str(ROOT/'solver.py'), str(request_path),
                              '--output', str(folder)], capture_output=True, text=True)
    require(process.returncode in (0, 2), 'Solver crashed: '+name+' '+process.stderr)
    result = json.loads((folder/'RESULT.json').read_bytes())
    require(result['status'] == expected, 'Wrong case verdict: '+name)
    verification = verify_result(folder/'RESULT.json', replay_backend=True)
    return {'name': name, 'status': result['status'], 'verification': verification,
            'exit_code': process.returncode, 'stdout': process.stdout,
            'result_sha256': hashlib.sha256((folder/'RESULT.json').read_bytes()).hexdigest()}


def tamper_case(name, result, optimized=False, replay=False, files=None):
    folder = ROOT/'tamper-checks'/name
    folder.mkdir(parents=True, exist_ok=True)
    for filename, content in (files or {}).items():
        (folder/filename).write_bytes(content)
    path = folder/'RESULT.json'
    path.write_text(json.dumps(result, indent=2)+'\n')
    command = [sys.executable]+(['-O'] if optimized else [])+[str(ROOT/'verify_certificate.py'), str(path)]
    if replay:
        command += ['--replay-backend']
    check = subprocess.run(command, capture_output=True, text=True)
    require(check.returncode == 1 and 'FAIL_CERTIFICATE' in check.stdout,
            'Accepted tampered certificate: '+name)
    return {'name': name, 'status': 'REJECTED_AS_REQUIRED', 'exit_code': check.returncode,
            'python_optimized': optimized, 'stdout': check.stdout}


def main():
    start = time.monotonic()
    core = sorted(ROOT.glob('*.py')) + [ROOT/'continuous_optimizer_normalized.wl']
    before = {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in core}
    # Exact upstream controls are freshly run, preserving their original bytes.
    upstream_checks = []
    for filename in ('verify.py', 'verify_census.py'):
        process = subprocess.run([sys.executable, str(ROOT/'upstream'/filename)],
                                 capture_output=True, text=True)
        require(process.returncode == 0, 'Upstream source controls failed: '+process.stderr)
        upstream_checks.append({'script': filename, 'exit_code': 0, 'stdout': process.stdout})
    cases = [
        ('triplet-sat', 'SAT_ONE_COHERENT_ADMITTED_SOURCE'),
        ('triplet-positive-boundary-unsat', 'UNSAT_COMPLETE_KNOWN_REGISTRY'),
        ('same-source-contradiction-unsat', 'UNSAT_COMPLETE_KNOWN_REGISTRY'),
        ('unknown-registry-rejected', 'UNKNOWN_UNSUPPORTED_OR_UNADMITTED_CONTRACT'),
        ('estimated-frequency-rejected', 'UNKNOWN_UNSUPPORTED_OR_UNADMITTED_CONTRACT'),
        ('negative-empirical-admission', 'UNKNOWN_UNSUPPORTED_OR_UNADMITTED_CONTRACT'),
        ('hybrid-common-sat', 'SAT_ONE_COHERENT_ADMITTED_SOURCE'),
        ('hybrid-independent-sat', 'SAT_ONE_COHERENT_ADMITTED_SOURCE'),
        ('joint-quartet-identification', 'IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY'),
        ('target-ambiguity', 'AMBIGUOUS_TARGET_TWO_ADMITTED_SOURCE_WITNESSES'),
        ('resource-incomplete', 'UNKNOWN_RESOURCE_LIMIT'),
        ('nonlinear-shared-row-unsat', 'UNSAT_COMPLETE_KNOWN_REGISTRY'),
        ('passive-quartet-policy', 'IDENTIFIED_TARGET_COMPLETE_KNOWN_REGISTRY'),
    ]
    results = [run_case(name, expected) for name, expected in cases]
    searches = []
    for name, extra, expected in (
        ('unknown-size-positive', 1, 'SAT_ADMITTED_SOURCE_UNKNOWN_SIZE_SEARCH'),
        ('unknown-size-bounded-no', 0, 'UNKNOWN_BOUNDED_SEARCH_EXHAUSTED')):
        folder = ROOT/'runs'/name
        process = subprocess.run([sys.executable, str(ROOT/'bounded_search.py'),
                                  str(ROOT/'examples'/f'{name}.json'), '--output', str(folder),
                                  '--max-extra-hybrids', str(extra)], capture_output=True, text=True)
        require(process.returncode in (0, 2), 'Bounded search crashed.')
        result = json.loads((folder/'SEARCH-RESULT.json').read_bytes())
        require(result['status'] == expected, 'Wrong bounded search verdict.')
        searches.append({'name': name, 'status': expected,
                         'verification': verify_search(folder/'SEARCH-RESULT.json', True)})

    # Several records from the SAME gene tree must retain their joint dependence.
    q = json.loads((ROOT/'examples/joint-quartet-identification.json').read_bytes())
    _, _, modes, _, rows = s.prepare_request(q)
    law = s.equations(next(s.census(4, 0)), modes[0], rows)[1][0]
    require(all(outcome[0] == outcome[1] for outcome in law), 'Same-tree readout lost correlation.')
    require(len(law) == 3 and all(p != 0 for p in law.values()), 'Missing quartet coordinates.')
    require(sum(law.values()) == 1, 'Joint law mass failure.')
    policy = execute(json.loads((ROOT/'examples/passive-quartet-policy.json').read_bytes()))
    (ROOT/'runs/PASSIVE-POLICY-RESULT.json').write_text(json.dumps(policy, indent=2)+'\n')
    design_request = json.loads((ROOT/'examples/four-taxon-passive-design.json').read_bytes())
    design = export(design_request, ROOT/'design-runs/four-taxon-passive')
    require(design['catalogue_exhausted'] and design['source_count_examined'] == 15,
            'Incomplete actual G7 source model export.')
    reduction = reduce_design(ROOT/'design-runs/four-taxon-passive-reduced')
    require(reduction['source_count'] == 15, 'Incomplete source image optimization.')

    sat = json.loads((ROOT/'runs/triplet-sat/RESULT.json').read_bytes())
    no = json.loads((ROOT/'runs/triplet-positive-boundary-unsat/RESULT.json').read_bytes())
    tamper = []
    bad = copy.deepcopy(sat); bad['entries'][0]['values']['x0'] = {'kind': 'rational', 'value': '1'}
    tamper.append(tamper_case('strict-boundary-witness', bad))
    bad = copy.deepcopy(sat); bad['entries'][0]['values']['x0'] = {'kind': 'rational', 'value': '1/4'}
    tamper.append(tamper_case('wrong-law-witness', bad, True))
    bad = copy.deepcopy(sat); bad['entries'][0]['equations'][0] = '0'
    bad['entries'][0]['equation_sha256'] = s.digest(bad['entries'][0]['equations'])
    tamper.append(tamper_case('forged-compiler-equations', bad))
    bad = copy.deepcopy(sat); bad['Lean_verification_claimed'] = True
    tamper.append(tamper_case('false-lean-promotion', bad, True))
    bad = copy.deepcopy(no); bad['entries'].pop()
    tamper.append(tamper_case('omitted-catalogue-entry', bad))
    bad = copy.deepcopy(no); bad['entries'][0]['certificate']['multipliers'] = ['0']*len(bad['entries'][0]['equations'])
    tamper.append(tamper_case('forged-linear-certificate', bad, True))
    bad = copy.deepcopy(sat)
    bad.update(status='UNSAT_COMPLETE_KNOWN_REGISTRY', catalogue_exhausted=True,
               verification='EXACT_BACKEND_PROOF_AND_REPLAY_REQUIRED')
    query = b'(assert false)\n(check-sat)\n'; proof = b'not-an-independent-proof\n'
    bad['entries'][0].update(status='UNSAT_EXACT_BACKEND_PROOF_NOT_INDEPENDENTLY_CHECKED',
                            query='fake.smt2', proof='fake.z3-proof',
                            query_sha256=hashlib.sha256(query).hexdigest(),
                            proof_sha256=hashlib.sha256(proof).hexdigest())
    tamper.append(tamper_case('forged-unsat-query', bad, True, True,
                             {'fake.smt2': query, 'fake.z3-proof': proof}))

    x = s.z3.Real('algebraic_roundtrip_x'); backend = s.z3.SolverFor('QF_NRA')
    backend.add(x*x == s.z3.RealVal('1/2'), x > 0, x < 1)
    require(backend.check() == s.z3.sat, 'Algebraic control backend failure.')
    encoded = s.encode_value(backend.model()[x]); decoded = s.decode_value(encoded)
    require(s.exact_zero(decoded**2-sp.Rational(1, 2))
            and decoded.is_positive and (1-decoded).is_positive,
            'Exact algebraic encoding failure.')
    invalid = []
    for name, mutate in (
        ('floating-probabilities', lambda q: q['rows'][0]['law'][0].update(p=0.5)),
        ('invalid-limits', lambda q: q['limits'].update(max_sources=0)),
        ('unencoded-parameter-ties', lambda q: q.update(parameter_constraints='x0=x1')),
        ('unchecked-positive-empirical-metadata', lambda q: q.update(empirical_admission={'status': 'ADMITTED'})),
        ('tied-clocks', lambda q: q.update(clock_contract='shared_clock')),
        ('unregistered-control', lambda q: q['rows'][0].update(forced={'missing_original_site': 0})),
        ('missing-mass', lambda q: q['rows'][0]['law'][0].update(p='1/2'))):
        bad = copy.deepcopy(sat['request']); mutate(bad)
        result = s.solve(bad, ROOT/'admission-checks'/name)
        require(result['status'] in ('INVALID_INPUT', 'UNKNOWN_UNSUPPORTED_OR_UNADMITTED_CONTRACT'),
                'Incorrectly admitted invalid experiment: '+name)
        invalid.append({'name': name, 'status': result['status'], 'reason': result['reason']})

    after = {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in core}
    require(before == after, 'Source bytes changed during end-to-end checks.')
    report = {'status': 'PASS_COMPLETE_PRACTICAL_SOLVER_CHECKPOINT',
              'entrypoint': ['python', 'tests.py'], 'terminal_exit': 0,
              'code_sha256_before_after': before,
              'software': {'python': sys.version.split()[0], 'sympy': sp.__version__,
                           'networkx': nx.__version__, 'z3': s.z3.get_version_string()},
              'upstream_checks': upstream_checks, 'cases': results, 'bounded_searches': searches,
              'same_genealogy_joint_dependence': 'PASS', 'policy_result_status': policy['status'],
              'actual_G7_model_export': design, 'actual_tree_source_image_reduction': reduction,
              'tamper_checks': tamper, 'algebraic_roundtrip': encoded,
              'invalid_admission_checks': invalid, 'elapsed_seconds': time.monotonic()-start,
              'scope': 'Reproducible software/source-instance controls; no universal proof by testing, independent external review or Lean verification inferred.'}
    (ROOT/'TEST-RECEIPT.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'source_cases': len(results),
                      'bounded_search_cases': len(searches), 'tamper_cases': len(tamper),
                      'upstream_exact_law_controls': 3336, 'terminal_exit': 0,
                      'elapsed_seconds': report['elapsed_seconds']}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
