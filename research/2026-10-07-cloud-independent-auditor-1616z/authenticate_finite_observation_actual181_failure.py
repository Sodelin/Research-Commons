"""Read-only terminal/Git/JSON authentication; never launches a source or compiler."""
from pathlib import Path
import base64
import collections
import gzip
import hashlib
import json
import re
import subprocess
import sys

REPO = Path('/workspace/g6-auditor')
ROOT = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/'
OWN = REPO / 'research/2026-10-07-cloud-independent-auditor-1616z'
FROZEN = 'ceadcd149cd3a7f093853815cad2489b91380ba7'
PRIOR = 'cdf4c4c0f9e0f6de59a7701b14656565a84cc481'
PRIOR_DIR = ROOT + 'verification/evidence/g6-run-37738512508-PASS/'
EVIDENCE = ROOT + 'verification/evidence/g6-run-37743712528-FAILED/'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git_bytes(commit, path):
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def git_record(commit, path):
    data = git_bytes(commit, path)
    blob = subprocess.check_output(['git', 'rev-parse', commit + ':' + path], cwd=REPO).decode().strip()
    assert blob == hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    return {'commit': commit, 'path': path, 'bytes': len(data), 'sha256': sha(data), 'git_blob_sha': blob}


def without_comments(text):
    # Import-looking prose inside nested Lean comments is not an import.
    out = []
    i = depth = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                out.append('\n')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i])
            i += 1
    assert not depth
    return ''.join(out)


def main():
    author = sys.argv[1]
    original_path = Path(sys.argv[2])
    original = original_path.read_bytes()
    assert len(original) == 2122053
    assert sha(original) == 'e892572c36ce96857d8f78431310c1755015843d4d3313b87840e2a2ce56fc63'
    # Exactly one optional OUTER BOM and timestamp separator. No general strip/lstrip.
    outer = re.compile(r'^\ufeff?\d{4}-\d{2}-\d{2}T\S+ ')
    original_lines = original.decode().splitlines()
    lines = [outer.sub('', line, count=1) for line in original_lines]
    normalized = ('\n'.join(lines) + '\n').encode()
    assert sha(normalized) == '404ec0c2428defaab1dc4092a47521a69e6d2fc450d5d48ecd1de60ff7fa8956'
    bom_lines = [i + 1 for i, line in enumerate(original_lines) if i and line.startswith('\ufeff')]
    assert bom_lines == [12147]
    inputs = next(json.loads(line[len('G6_INPUTS '):]) for line in lines if line.startswith('G6_INPUTS '))
    assert inputs['source_commit'] == FROZEN
    plan = json.loads(git_bytes(FROZEN, ROOT + 'verification/freeze-plans/finite-observation-actual179-static.json'))
    assert len(inputs['modules']) == plan['custom_modules'] == 181
    assert inputs['targets'] == plan['targets'] and len(inputs['targets']) == 47
    assert inputs['mathlib_roots'] == plan['mathlib_roots']
    assert set(inputs['modules']) == set(plan['modules'])
    sources = {}
    source_records = {}
    for name, record in inputs['modules'].items():
        path = plan['modules'][name]['repository_path']
        data = git_bytes(FROZEN, path)
        assert sha(data) == record['sha256'] == plan['modules'][name]['sha256']
        imports = re.findall(r'^import\s+(\S+)', without_comments(data.decode()), re.M)
        assert imports == record['imports']
        sources[name] = data.decode()
        source_records[name] = git_record(FROZEN, path)
    receipts = [json.loads(line[len('G6_RECEIPT '):]) for line in lines if line.startswith('G6_RECEIPT ')]
    assert len(receipts) == 183 and sum(r['exit'] == 0 for r in receipts) == 182
    outputs = {}
    output_records = {}
    failed = []
    for i, line in enumerate(lines):
        if not line.startswith('G6_COMMAND '):
            continue
        command = json.loads(line[len('G6_COMMAND '):])
        end = next(j for j in range(i + 1, len(lines)) if lines[j].startswith('G6_RECEIPT '))
        receipt = json.loads(lines[end][len('G6_RECEIPT '):])
        assert command['argv'] == receipt['argv']
        if command['argv'][:4] == ['lake', 'exe', 'cache', 'get']:
            continue
        body = lines[i + 1:end]
        data = ('\n'.join(body) + ('\n' if body else '')).encode()
        assert sha(data) == receipt['output_sha256'], command['argv']
        name = command['argv'][-1].rsplit('/', 1)[-1]
        assert name not in outputs
        outputs[name] = data
        output_records[name] = {'bytes': len(data), 'sha256': sha(data), 'exit': receipt['exit'], 'argv': command['argv']}
        if receipt['exit']:
            failed.append(name)
    assert len(outputs) == 182 and failed == ['FiniteCorruptionBoundary.lean']
    assert outputs['HybridSizeCore.lean'] == b''
    counts = next(json.loads(line[len('CLOUD_SELECTED_AXIOM_AUDIT_PASSED '):]) for line in lines if line.startswith('CLOUD_SELECTED_AXIOM_AUDIT_PASSED '))
    assert len(counts) == 45 and sum(counts.values()) == 501
    named = {}
    for name in inputs['targets']:
        if name not in counts:
            continue
        namespace = re.search(r'^namespace\s+(\S+)\s*$', sources[name], re.M)
        assert namespace
        named[name] = [namespace[1] + '.' + n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_']+)", sources[name], re.M)]
    assert {name: len(rows) for name, rows in named.items()} == counts
    names = [name for rows in named.values() for name in rows]
    audit_text = outputs['DeclarationAudit.lean'].decode()
    reports = {n: [a.strip() for a in axes.split(',') if a.strip()] for n, axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_text, re.S)}
    reports.update({n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", audit_text)})
    assert len(names) == len(set(names)) == 501 and set(names) == set(reports)
    assert all(set(axes) <= STANDARD for axes in reports.values())
    named_source = '\n'.join('import ' + name for name in named) + '\n\n' + '\n'.join('#print axioms ' + name for name in names) + '\n'
    payload = next(json.loads(line[len('G6_COMPLETE_ENVIRONMENT_PAYLOAD '):]) for line in lines if line.startswith('G6_COMPLETE_ENVIRONMENT_PAYLOAD '))
    begin = lines.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN')
    end = lines.index('G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END')
    payload_lines = lines[begin + 1:end]
    base64_lines = [line for line in payload_lines if re.fullmatch(r'[A-Za-z0-9+/]+={0,2}', line)]
    discarded = [line for line in payload_lines if line not in base64_lines]
    assert discarded == ['Selected source failure: [{"module": "UnifiedLean.G6.FiniteCorruptionBoundary", "result": "1"}]']
    raw = gzip.decompress(base64.b64decode(''.join(base64_lines), validate=True))
    assert len(raw) == payload['bytes'] == 6430249 and sha(raw) == payload['sha256']
    assert sha(raw) == 'cf0a500c9e35831cd598d6f12edd4fc0e63b534a2ad4322eb6584981307944ba'
    assert raw == git_bytes(PRIOR, PRIOR_DIR + 'complete-environment-inventory.json')
    inventory = json.loads(raw)
    rows = inventory['declarations']
    assert inventory['declaration_count'] == len(rows) == 4209
    assert inventory['theorem_declaration_count'] == sum(r['kind'] == 'theorem' for r in rows) == 2766
    assert len({r['name'] for r in rows}) == len(rows)
    assert not inventory['owned_axioms'] and not inventory['nonstandard_axiom_rows'] and not inventory['missing_modules']
    assert len(inventory['selected_modules']) == 179
    excluded = {'UnifiedLean.G6.FiniteCorruptionBoundary', 'ActualObservationCorruption'}
    assert set(inventory['selected_modules']) == set(inputs['modules']) - excluded
    assert all(r['module'] in inventory['selected_modules'] and set(r['axioms']) <= STANDARD and 'type_references' in r and 'body_references' in r for r in rows)
    prior_inputs = json.loads(git_bytes(PRIOR, PRIOR_DIR + 'inputs-recovered.json'))
    assert all(inputs['modules'][n] == r for n, r in prior_inputs['modules'].items())
    assert inputs['topological_order'][:179] == prior_inputs['topological_order']
    template = git_bytes(FROZEN, 'research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean').decode()
    old = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
    assert template.count(old) == 1
    template = template.replace(old, '#[' + ', '.join(json.dumps(n) for n in inventory['selected_modules']) + ']')
    complete_source = '\n'.join('import ' + n for n in inventory['selected_modules']) + '\n' + template
    assert sha(complete_source.encode()) == payload['audit_source_sha256'] == '2fd8f63e5618d1a856edf9252683e14ae130d2844c170d942d09758f40fbb47a'
    failed_text = outputs['FiniteCorruptionBoundary.lean'].decode()
    errors = re.findall(r'FiniteCorruptionBoundary\.lean:(\d+):(\d+): error:', failed_text)
    assert errors == [('32', '16'), ('49', '49')]
    assert failed_text.count('sorryAx') == 7
    assert 'ActualObservationCorruption.lean' not in outputs
    # Exact public author correspondence, including the unchanged original transport.
    author_paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', author, EVIDENCE], cwd=REPO).decode().splitlines()
    assert author_paths
    artifact_records = [git_record(author, p) for p in author_paths]
    def authored(name):
        return git_bytes(author, EVIDENCE + name)
    assert authored('original-connector-job.log') == original
    assert authored('actions.log') == normalized
    assert json.loads(authored('inputs-recovered.json')) == inputs
    assert json.loads(authored('receipts-recovered.json')) == receipts
    assert authored('complete-environment-inventory.json') == raw
    assert authored('DeclarationAudit-reconstructed.lean') == named_source.encode()
    assert authored('CompleteEnvironmentAudit-reconstructed.lean') == complete_source.encode()
    author_audit = json.loads(authored('axiom-audit-recovered.json'))
    assert author_audit['transitive_axioms'] == reports and author_audit['declarations_by_module'] == named
    assert author_audit['module_counts'] == counts and author_audit['named_declarations'] == names
    assert author_audit['named_stdout_sha256'] == sha(outputs['DeclarationAudit.lean'])
    assert author_audit['named_source_sha256'] == sha(named_source.encode())
    assert author_audit['custom_and_audit_stdout_readback'] == {n: sha(b) for n, b in outputs.items()}
    for p in author_paths:
        if p.endswith('-actual.log'):
            n = p.rsplit('/', 1)[-1][:-len('-actual.log')] + '.lean'
            assert authored(p.rsplit('/', 1)[-1]) == outputs[n]
    complete_receipt = json.loads(authored('complete-ownership-receipt.json'))
    assert complete_receipt['payload'] == payload
    assert complete_receipt['interleaved_stderr_lines'] == discarded
    assert complete_receipt['all_owned_counts_by_module'] == dict(collections.Counter(r['module'] for r in rows))
    assert complete_receipt['all_owned_counts_by_kind'] == dict(collections.Counter(r['kind'] for r in rows))
    run = json.loads(authored('run.json'))
    assert run['id'] == 37743712528 and run['head_sha'] == FROZEN and run['status'] == 'completed' and run['conclusion'] == 'failure'
    jobs = json.loads(authored('jobs.json'))
    job = next(j for j in jobs['jobs'] if j['id'] == 113200145025)
    assert job['status'] == 'completed' and job['conclusion'] == 'failure'
    record = {
        'status': 'PRIMARY exact actual FAILED terminal/retained179 scope + public author correspondence ACCEPT',
        'run': 37743712528, 'frozen_input': FROZEN, 'job': 113200145025,
        'author_commit': author, 'original_connector_bytes': len(original), 'original_connector_sha256': sha(original),
        'corrected_actions_sha256': sha(normalized), 'outer_interior_bom_lines': bom_lines,
        'normalization': 'Remove ONLY optional outer BOM/timestamp plus exactly one separator; preserve Lean indentation and empty output.',
        'command_receipts': len(receipts), 'zero_exit_receipts': 182, 'noncache_stdout_exact': len(outputs),
        'requested_custom': 181, 'successful_custom': 179, 'named_reports': 501,
        'named_scope': {'G6': 352, 'G3': 134, 'G5': 15},
        'complete_owned': 4209, 'complete_theorems': 2766, 'prior4209_all_bytes_exact': True,
        'payload': payload, 'failed_entire_modules': ['UnifiedLean.G6.FiniteCorruptionBoundary'],
        'blocked_modules': ['ActualObservationCorruption'], 'actual_error_positions': errors,
        'failed_sorryAx_reports_wholly_excluded': 7, 'interleaved_stderr_preserved': discarded,
        'source_records': source_records, 'output_records': output_records, 'author_artifact_records': artifact_records,
        'standard_axioms_only': True, 'historical_calendarTail_helper_exception_retained': True,
        'run_updated_at': run['updated_at'], 'job_started_at': job['started_at'], 'job_completed_at': job['completed_at'],
        'cache_command_stdout_comparison': False, 'archive_comparison': False,
        'compiler_invoked': False, 'source_evaluated': False, 'Actions_polled': False,
        'terminal_known_completed_job_log_retrieved_once': True,
    }
    out = OWN / 'finite-observation-actual181-terminal-authentication.json'
    out.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps({k: v for k, v in record.items() if k not in {'source_records', 'output_records', 'author_artifact_records'}}, indent=2))


if __name__ == '__main__':
    main()
