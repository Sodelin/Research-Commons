"""Replay the exact G4 controls. No floating-point tolerance decides equality.

Run from a checkout: python replay.py --output-dir replay-results
Requires networkx and sympy. Every subprocess must finish successfully.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', default='replay-results')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Do not use Python -O: these controls use assertions.')
    root = Path(__file__).resolve().parent
    destination = Path(args.output_dir).expanduser().resolve()
    destination.mkdir(parents=True, exist_ok=True)
    jobs: list[list[str]] = []
    for cap in (3, 4, 5):
        for mode in ('common', 'independent', 'paired'):
            output = destination / f'algebra-cap{cap}-{mode}.json'
            jobs.append([sys.executable, str(root / 'forest_algebra.py'),
                         '--cap', str(cap), '--mode', mode, '--output', str(output)])
    for script, filename in (('source_checks.py', 'source-checks.json'),
                             ('adversarial_checks.py', 'adversarial-checks.json')):
        jobs.append([sys.executable, str(root / script), '--output', str(destination / filename)])
    started = datetime.now(timezone.utc).isoformat()
    for job in jobs:
        print('Running', Path(job[1]).name, ' '.join(job[2:]), flush=True)
        completed = subprocess.run(job, cwd=root, text=True, capture_output=True, check=False)
        if completed.returncode:
            print(completed.stdout, file=sys.stderr)
            print(completed.stderr, file=sys.stderr)
            raise SystemExit(f'Failed: {job[1]} (exit {completed.returncode}). No success receipt written.')
    import networkx
    import sympy
    receipt = {
        'session': 'ASTRA-G4-TESTERS-20261001-0819Z',
        'started_utc': started,
        'finished_utc': datetime.now(timezone.utc).isoformat(),
        'python': platform.python_version(),
        'networkx': networkx.__version__,
        'sympy': sympy.__version__,
        'completed_jobs': len(jobs),
        'all_jobs_returned_zero': True,
        'files': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in sorted(destination.glob('*.json')) if p.name != 'REPLAY-RECEIPT.json'},
        'not_certified': ['Exhaustive bounded-core enumeration',
                          'General positive independent collision elimination',
                          'General timed-core compiler',
                          'Unbounded-copy independent-source equality stopping',
                          'Independent review or formal verification'],
    }
    (destination / 'REPLAY-RECEIPT.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
