"""Authenticate the author packet against independently fetched terminal bytes; no compiler."""
from pathlib import Path
import gzip, hashlib, json, re, subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[1]
PREFIX = 'natural-family-repair-attempt-37720559518'
AUTHOR = '993d2a4dd6e3bb34f57f5b1d9396db91e4e7161c'
PUBLIC = 'research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37720559518-FAILED/'
sha = lambda b: hashlib.sha256(b).hexdigest()
def git(path):
    return subprocess.check_output(['git', 'show', AUTHOR + ':' + path], cwd=ROOT)
def extract(raw):
    msgs = [re.sub(r'^\d{4}-\d\d-\d\dT\S+Z ?', '', l.split('\t', 2)[-1].lstrip('\ufeff')) for l in raw.decode().splitlines()]
    inputs = next(json.loads(m.split(' ', 1)[1]) for m in msgs if m.startswith('G6_INPUTS '))
    receipts, out, pending, lines = [], {}, None, []
    for msg in msgs:
        if msg.startswith('G6_COMMAND '):
            assert pending is None
            pending = json.loads(msg.split(' ', 1)[1]); lines = []
        elif msg.startswith('G6_RECEIPT '):
            assert pending is not None
            r = json.loads(msg.split(' ', 1)[1])
            label = Path(r['argv'][-1]).stem if r['argv'][1:3] == ['env', 'lean'] else 'cache'
            out[label] = ('\n'.join(lines) + ('\n' if lines else '')).encode()
            receipts.append(r); pending = None
        elif pending is not None:
            lines.append(msg)
    assert pending is None
    return inputs, receipts, out

official = (BASE / (PREFIX + '-actions.log')).read_bytes()
author_original = git(PUBLIC + 'connector-job-original.log')
author_outer = git(PUBLIC + 'actions.log')
assert official == author_original
i, receipts, out = extract(official)
ai, ar, ao = extract(author_outer)
assert i == ai and receipts == ar and len(receipts) == 176
assert json.loads(git(PUBLIC + 'inputs-recovered.json')) == i
assert json.loads(git(PUBLIC + 'receipts-recovered.json')) == receipts
correspondence = []
for label, data in out.items():
    if label == 'cache': continue
    assert ao[label] == data
    correspondence.append({'label': label, 'stdout_sha256': sha(data), 'byte_equal': True})
assert len(correspondence) == 175
ind = json.loads((BASE / (PREFIX + '-independent.json')).read_text())
raw = (BASE / (PREFIX + '-inventory.json')).read_bytes()
checks = []
data_files = [('connector-job-original.log', official), ('complete-environment-inventory.json', raw),
              ('DeclarationAudit-actual.log', out['DeclarationAudit']),
              ('DeclarationAudit-reconstructed.lean', (BASE / (PREFIX + '-DeclarationAudit.lean')).read_bytes()),
              ('CompleteEnvironmentAudit-reconstructed.lean', (BASE / (PREFIX + '-CompleteEnvironmentAudit.lean')).read_bytes())]
data_files += [(n + '-actual.log', out[n]) for n in ['PrivateRegisterSourceStep','PrivateRegisterBoundary','PrivateRegisterProgram','PrivateRegisterHistory','PrivateSeedFactorization','PrivateRegisterCalendar']]
paths = subprocess.check_output(['git','ls-tree','-r','--name-only',AUTHOR,PUBLIC],cwd=ROOT).decode().splitlines()
artifact_checks=[]
for path in paths:
    data=git(path)
    artifact_checks.append({'path':path,'bytes':len(data),'sha256':sha(data),'git_blob':hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()})
assert len(artifact_checks)==59
for name, data in data_files:
    assert git(PUBLIC + name) == data, name
    checks.append({'path': PUBLIC + name, 'sha256': sha(data), 'byte_equal': True})
result = {'author_commit': AUTHOR, 'original_connector_log_sha256': sha(official),
          'original_connector_job_log_byte_equal': True, 'author_outer_log_sha256': sha(author_outer),
          'normalized_outer_log_byte_equal': official == author_outer,
          'all176_command_receipts_equal': True, 'all175_noncache_stdout_byte_equal': correspondence,
          'input_manifest_equal': True, 'source_and_full_inventory_audits_reconstructed_from_frozen_inputs': True,
          'author_all59_artifacts_readback':artifact_checks,'author_exact_data_files': checks, 'archive_transport_attempted': False, 'compiler_invoked': False}
(BASE / (PREFIX + '-author-correspondence.json')).write_text(json.dumps(result, indent=2) + '\n')
ind['author_publication_commit'] = AUTHOR
ind['author_readback_checks'] = checks
ind['author_official_correspondence_file'] = PREFIX + '-author-correspondence.json'
(BASE / (PREFIX + '-independent.json')).write_text(json.dumps(ind, indent=2) + '\n')
print(json.dumps({'author_commit': AUTHOR, 'receipts': len(receipts), 'noncache_stdout': len(correspondence),
                  'original_log_byte_equal': True, 'raw_inventory_sha256': sha(raw), 'exact_data_files': len(checks)}))
