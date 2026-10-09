"""Generate rational proposals; exact standalone checker is the acceptance gate.

Run from repository root with the workbench directory on PYTHONPATH. Frozen
published providers are executed read-only; earlier failure is preserved.
"""
import argparse
import contextlib
from hashlib import sha256
import io
import json
from pathlib import Path
import runpy
import subprocess
import sys

from genealogy_workbench.g4_certificates import digest, check_cone, search_separator, LOCAL_PROOF_SHA256

ROOT = Path(__file__).resolve().parents[3]
PACKET = Path(__file__).resolve().parent
OUTPUT = PACKET
SOURCE = ROOT/'research/2026-10-09-dot-reviewed-guard-boundaries-1615z/g4'


def save(name, data):
    (OUTPUT/name).write_text(json.dumps(data, indent=2)+'\n')


def main():
    global OUTPUT
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=PACKET,
                        help='Use a fresh scratch directory to preserve published evidence')
    OUTPUT = parser.parse_args().output.resolve()
    OUTPUT.mkdir(parents=True, exist_ok=True)
    receipt = []
    for stem in ('certify_biased_cone_12', 'certify_biased_cone_12_before_generator_fix'):
        path = SOURCE/(stem+'.py')
        run = subprocess.run([sys.executable, str(path)], cwd=ROOT, capture_output=True,
                             text=True, timeout=30)
        (OUTPUT/(stem+'.stdout')).write_text(run.stdout)
        (OUTPUT/(stem+'.stderr')).write_text(run.stderr)
        receipt.append({'command': ['python3', str(path.relative_to(ROOT))],
                        'exit': run.returncode, 'source_sha256': sha256(path.read_bytes()).hexdigest(),
                        'stdout_sha256': sha256(run.stdout.encode()).hexdigest(),
                        'stderr_sha256': sha256(run.stderr.encode()).hexdigest()})
        if stem == 'certify_biased_cone_12':
            assert run.returncode == 0
            assert run.stdout.encode() == (SOURCE/'biased-cone-12-certificate.json').read_bytes()
        else:
            assert run.returncode != 0 and 'AssertionError' in run.stderr
    save('frozen-provider-replay.json', receipt)
    # The old provider exposes rational candidate integers; mpmath only proposed them.
    with contextlib.redirect_stdout(io.StringIO()):
        proposed = runpy.run_path(str(SOURCE/'certify_biased_cone_12.py'))
    request = {'kind': 'finite_log_diagonal_cone_v1', 'arities': list(range(2, 13)),
               'target': {'q': '1/2', 'g': '1/4'},
               'nodes': [{'q': q, 'g': g} for q, g in proposed['nodes']],
               'clock_min': '2/5', 'log_scale_digits': 100, 'atanh_terms': 120}
    certificate = {'kind': 'rational_preconditioned_cone_v1', 'request_sha256': digest(request),
                   'proposal_scale_digits': 60,
                   'inverse_integers': [[str(x) for x in row] for row in proposed['Bi']],
                   'weight_integers': [str(x) for x in proposed['wi']]}
    save('cone-request.json', request)
    save('cone-certificate.json', certificate)
    save('cone-replay.json', check_cone(request, certificate))
    local_request = {'kind': 'rational_local_weak_separator_v1', 'target_q': '1/2',
                     'target_p': '3/16', 'common_clock': '2/5', 'provider_sha256': LOCAL_PROOF_SHA256}
    save('local-request.json', local_request)
    search = search_separator(local_request, max_arity=10, max_degree=30)
    save('local-search.json', search)
    assert search['status'] == 'CERTIFIED_PROPOSAL_FOUND'
    save('local-certificate.json', search['certificate'])
    save('local-replay.json', search['checked'])
    print('PASS frozen corrected replay, preserved failure, request-bound cone, and bounded rational local search')


if __name__ == '__main__':
    main()
