"""Read-only retrieval of original stopped G5 compiler evidence inside runner.

The Cloud shell cannot reach Azure artifact downloads. This reuses the existing
artifact, checks the previously logged exact failure-output hash, and prints the
actual diagnostic. It does not run a compiler, restart G5, or alter its inputs.
"""
import datetime
import hashlib
import json
from pathlib import Path
import subprocess
import sys

destination = Path(sys.argv[1]).resolve()
destination.mkdir(parents=True, exist_ok=True)
original = destination / 'artifact'
receipt = {
    'source_run': 37650073193,
    'source_commit': 'a5a80af1dedc53ff060f8d521b50596851261cd4',
    'artifact_id': 11496078569,
    'reported_artifact_zip_sha256': '439aac618c7896cd34a9b5365e8a9553a5389e451e527368c24e341ac7d20f12',
    'expected_failed_stdout_sha256': '34de6290607f742b7e7e67716ddf0a40bace5fcd605fcedac473905952442717',
    'start': datetime.datetime.now(datetime.timezone.utc).isoformat(),
}
command = ['gh', 'run', 'download', '37650073193', '--repo', 'Sodelin/Research-Commons',
           '--name', 'cloud-g5-37650073193', '--dir', str(original)]
receipt['command'] = command
try:
    process = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=180)
    receipt['retrieval_exit'] = process.returncode
except subprocess.TimeoutExpired:
    receipt['retrieval_exit'] = 124

# Do not publish error messages containing temporary signed URLs or credentials.
diagnostics = list(original.rglob('G5FrozenTripleAnalyticSupport.log')) if original.exists() else []
receipt['diagnostic_found'] = len(diagnostics) == 1
if receipt['diagnostic_found']:
    diagnostic = diagnostics[0].read_bytes()
    receipt['observed_failed_stdout_sha256'] = hashlib.sha256(diagnostic).hexdigest()
    receipt['original_hash_matches'] = (
        receipt['observed_failed_stdout_sha256'] == receipt['expected_failed_stdout_sha256'])
    if receipt['original_hash_matches']:
        print('G5_ORIGINAL_FAILED_DIAGNOSTIC_BEGIN', flush=True)
        print(diagnostic.decode(errors='replace'), end='', flush=True)
        print('G5_ORIGINAL_FAILED_DIAGNOSTIC_END', flush=True)
        for name in ['module-results.json', 'commands.json', 'SOURCE-CONTEXT.json']:
            matches = list(original.rglob(name))
            if len(matches) == 1:
                print('G5_ORIGINAL_' + name + ' ' + matches[0].read_text(), flush=True)
receipt['end'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
(destination / 'retrieval-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('G5_ORIGINAL_RETRIEVAL ' + json.dumps(receipt), flush=True)
