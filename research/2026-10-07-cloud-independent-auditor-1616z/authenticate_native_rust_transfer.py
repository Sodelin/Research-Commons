"""Static frozen Git/receipt/closed-form checks; no Rust or supplied code runs."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import factorial
import subprocess, hashlib, json, tomllib, re

C = 'f32e04272b87e238685117939e0a25d6bbcc26d1'
P = 'research/2026-10-07-cloud-practical-native-rust-transfer-2358z/'
N = 'research/2026-10-07-rust-count-pilot/'
O = Path('research/2026-10-07-cloud-independent-auditor-1616z')
sha = lambda b: hashlib.sha256(b).hexdigest()
def raw(path, commit=C):
    return subprocess.check_output(['git', 'show', commit + ':' + path])
def blob(b):
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()
def read(path):
    return raw(P + path)

transfer = json.loads(read('TRANSFER.json'))
publication = json.loads(read('PUBLICATION.json'))
public = json.loads(read('PUBLIC-FILES.json'))
assert transfer['file_count'] == publication['file_count'] == 34
assert transfer['total_bytes'] == publication['total_bytes'] == 1225944
assert transfer['prefix'] == N.rstrip('/')
rows = transfer['files']
assert len({r['path'] for r in rows}) == len(rows) == 34
checked = []
for row, pub in zip(rows, publication['files']):
    b = raw(N + row['path'])
    assert sha(b) == row['sha256'] == pub['sha256']
    assert len(b) == row['bytes'] == pub['bytes']
    assert blob(b) == row['git_blob_sha'] == pub['git_blob_sha']
    mode = subprocess.check_output(['git', 'ls-tree', C, N + row['path']]).split()[0].decode()
    assert mode == row['file_mode'] == pub['file_mode'] == '100644'
    assert raw(N + row['path'], publication['publication_commit']) == b
    b.decode('utf-8')
    checked.append(dict(row, immutable_identity_and_original_attachment_equal=True))
assert sum(r['bytes'] for r in rows) == 1225944
actual_paths = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', C, N]).decode().splitlines()
assert set(actual_paths) == {N + r['path'] for r in rows}
note = raw(transfer['ownership_note'])
assert sha(note) == transfer['ownership_note_sha256']
note_manifest = json.loads(re.search(r'```json\n(.*?)\n```', note.decode(), re.S).group(1))
assert note_manifest['files'] == [{k:r[k] for k in ['path','git_blob_sha','sha256','bytes']} for r in rows]
public_checked = []
for r in public['files']:
    b = read(r['path'])
    assert sha(b) == r['sha256'] and len(b) == r['bytes']
    public_checked.append(dict(r, immutable_byte_identity=True))
assert public['original_native_payload_count'] == 34
assert len(public_checked) == 18
result_b = read('cloud-attempt1/RESULT.json')
r = json.loads(result_b)
assert sha(result_b) == '51c84b9884dc266757a27d8690f9a5543d731c7b7c6d4bd75d1b4654c694f09b'
assert r['script_sha256'] == sha(read('rebuild_native.py')) == 'f7226d1a0ed7b09a77b101cadf2ab6d2f58d01fba99d210560f796bfe7745f64'
assert r['source_publication_commit'] == publication['publication_commit']
assert read('cloud-attempt1/rustc-version.txt').decode().strip() == r['toolchain_rustc']
assert read('cloud-attempt1/cargo-version.txt').decode().strip() == r['toolchain_cargo']
assert '1159e78c4747b02ef996e55082b704c09b970588' in r['toolchain_rustc']
lock = tomllib.loads(raw(N + 'Cargo.lock').decode())
cache = json.loads(read('cloud-attempt1/CACHE.json'))
expected_cache = [{k:v[k] for k in ['name','version','checksum']} for v in lock['package'] if 'checksum' in v]
assert cache == r['cached_pinned_dependencies'] == expected_cache and len(cache) == 5
for e in r['executions']:
    name = e['name']
    assert json.loads(read('cloud-attempt1/' + name + '-EXECUTION.json')) == e
    assert e['exit'] == 0 and e['external_failure'] is None
    assert sha(read('cloud-attempt1/' + name + '.stdout')) == e['stdout_sha256']
    assert sha(read('cloud-attempt1/' + name + '.stderr')) == e['stderr_sha256']
    assert '--offline' in e['command'] and '--locked' in e['command']
    assert e['cpu_seconds_limit'] == 30 and e['wall_seconds_limit'] == 45
    assert e['address_space_bytes_limit'] == 2 * 1024**3
assert '10 passed; 0 failed' in read('cloud-attempt1/unit_tests.stdout').decode()
assert r['unit_tests_passed'] == 10
assert json.loads(read('cloud-attempt1/replay.stdout')) == r['replay']
assert read('cloud-attempt1/replay.stderr') == b''
assert r['replay']['status'] == 'PASS'
assert r['replay']['saved_complete_byte_exact_cases'] == 1693
assert r['replay']['invalid_cli_cases'] == 22 and r['replay']['additional_boundaries'] == 5
old = json.loads(raw(N + 'evidence/root-rebuild/REBUILD-RECEIPT.json'))
assert old['binary_sha256'] != r['binary_sha256'] and r['matches_reported_dot_root_binary'] is False
assert r['binary_sha256'] == '8a0df53da5dc58f3cb07ad1bbf4b7ea8d55be6e6edb17ad897269c1626458688'
assert r['benchmark_run'] is False and r['binary_published'] is False
corpus_b = raw(N + 'evidence/corpus.jsonl')
assert sha(corpus_b) == r['replay']['corpus_sha256']
corpus = [json.loads(line) for line in corpus_b.splitlines()]
assert len(corpus) == 1693
statuses = Counter()
for v in corpus:
    a, eps, e, budget = F(v['a']), F(v['epsilon']), v['expected'], v['max_steps']
    assert a >= 0 and 0 < eps < 1
    k = e.get('K', e.get('next_K'))
    assert isinstance(k, int) and 0 <= k <= 199
    # Closed-form rational powers/factorials, independent of production recurrence.
    ts = [a**j / factorial(j) for j in range(k + 2)]
    def qualifies(j):
        s = sum(ts[:j+1], F(0)); t = ts[j+1]
        return j + 2 >= 2*a and 2*t/(s+2*t) <= eps
    expected = {'a':str(a), 'epsilon':str(eps), 'law':'normalized_prefix'}
    if e['status'] == 'CERTIFIED':
        assert all(not qualifies(j) for j in range(k)) and qualifies(k)
        assert budget is None or k + 1 <= budget
        s, t = sum(ts[:k+1], F(0)), ts[k+1]
        expected.update(K=k, S=str(s), T=str(t), U=str(s+2*t), delta=str(2*t/(s+2*t)), inspected=k+1, status='CERTIFIED')
        if v['weights']: expected['weights'] = [str(ti/s) for ti in ts[:k+1]]
    else:
        assert e['status'] == 'RESOURCE_LIMIT' and k == budget
        assert all(not qualifies(j) for j in range(k))
        expected.update(inspected=k, next_K=k, status='RESOURCE_LIMIT')
    assert expected == e
    statuses[e['status']] += 1
subprocess.run(['git','merge-base','--is-ancestor',C,'origin/main'],check=True)
out = {'status':'SOURCE/CODE ACCEPT and inspected author-execution correspondence',
       'author_commit':C, 'transferred_original_files':checked,
       'transferred_original_total_bytes':1225944, 'ownership_note_sha256':sha(note),
       'public_cloud_payload_pins':public_checked, 'result_sha256':sha(result_b),
       'actual_author_receipt':r, 'reviewer_static_closed_form_corpus_objects':len(corpus),
       'reviewer_static_expected_status_counts':dict(statuses),
       'reviewer_executed_native_binary_Cargo_reference_harness_or_supplied_code':False,
       'limits':['Source review plus finite saved-receipt validation, not universal implementation equivalence.',
                 'Recorded actual executions are author executions. Individual native stdout was not separately archived by the replay runner; its PASS summary is corroborated by reviewed loop and frozen expected corpus.',
                 'Native executable is not published, and no independent source-to-binary attestation, rebuild, byte reproducibility, benchmark, Rust1.74 or other-platform claim is issued.',
                 'No scientific admission, whole JC inverse/useful cover, full practical solver or G6 closure.']}
(O/'native-rust-transfer-rebuild-source-receipt-authentication.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':out['status'],'transfer_files':len(checked),'cloud_payloads':len(public_checked),'static_closed_form_objects':len(corpus),'static_status_counts':dict(statuses),'result_sha256':sha(result_b)},indent=2))
