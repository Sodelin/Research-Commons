#!/usr/bin/env python3
"""RAM-only Node result capture; seal with the existing verified pipe codec."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from peer_message import seal


def main():
    arguments = sys.argv[1:]
    drain = bool(arguments and arguments[0] == '--drain-report')
    if drain:
        arguments = arguments[1:]
    core = Path(__file__).with_name('online_lean_quiet.mjs')
    client = Path(__file__).with_name('online_lean_drain.mjs') if drain else core
    client_sha_before = hashlib.sha256(client.read_bytes()).hexdigest()
    core_sha_before = hashlib.sha256(core.read_bytes()).hexdigest()
    capture_failure = None
    try:
        completed = subprocess.run(['node', str(client), *arguments],
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   timeout=130, check=False)
        captured_stdout, captured_stderr = completed.stdout, completed.stderr
        client_exit = completed.returncode
    except subprocess.TimeoutExpired as error:
        # These partial pipes remain in memory until sealed below. A timeout
        # cannot be accepted even if a partial stream contains a success word.
        captured_stdout, captured_stderr = error.stdout or b'', error.stderr or b''
        client_exit, capture_failure = None, 'PARENT_CAPTURE_TIMEOUT'
    except OSError:
        captured_stdout, captured_stderr = b'', b''
        client_exit, capture_failure = None, 'CLIENT_PROCESS_UNAVAILABLE'
    try:
        result = json.loads(captured_stdout)
    except (ValueError, UnicodeError):
        result = {'status': 'UNVERIFIED', 'reason': 'CLIENT_RESULT_UNREADABLE'}
    if capture_failure:
        result = {'status': 'UNVERIFIED', 'reason': capture_failure}
    client_sha_after = hashlib.sha256(client.read_bytes()).hexdigest()
    core_sha_after = hashlib.sha256(core.read_bytes()).hexdigest()
    client_unchanged = client_sha_before == client_sha_after and core_sha_before == core_sha_after
    if not client_unchanged:
        result = {'status':'UNVERIFIED','reason':'CLIENT_SOURCE_CHANGED_DURING_CAPTURE'}
    receipt, _ = seal({'client_sha256': client_sha_before,
                       'client_sha256_after': client_sha_after,
                       'client_entry': client.name,
                       'core_client_sha256': core_sha_before,
                       'core_client_sha256_after': core_sha_after,
                       'client_identity_unchanged': client_unchanged,
                       'client_exit': client_exit, 'capture_failure': capture_failure,
                       'original_stdout': captured_stdout.decode('utf-8', errors='replace'),
                       'original_stderr': captured_stderr.decode('utf-8', errors='replace')})
    errors = [json.loads(d) for d in dict.fromkeys(json.dumps(
                    {'range': d.get('range'), 'message': d.get('message')}, sort_keys=True)
                   for d in result.get('errors', []))]
    # The complete original streams have already been encrypted above. Only
    # this routine console projection is bounded; no diagnostic is removed
    # from the captured client result or its acceptance decision.
    print(json.dumps({'status': result['status'], 'reason': result.get('reason'),
        'error_count': len(errors),
        'errors': [{'range':d['range'],'message':(d['message'] or '')[:1500]} for d in errors[:3]],
        'display_errors_truncated': len(errors)>3 or any(len(d['message'] or '')>1500 for d in errors[:3]),
        'warning_count': len(result.get('warnings', [])),
        'audits': [{'name': d['name'], 'clean': d['clean']}
                   for d in result.get('audit_rows', [])],
        'versions': result.get('before'), 'receipt': receipt,
        'local_compiler': False, 'lake_build': False}, sort_keys=True))
    return 0 if client_exit == 0 and result['status'] == 'PASS_REMOTE_LEAN_CHECK' else 2


if __name__ == '__main__':
    sys.exit(main())
