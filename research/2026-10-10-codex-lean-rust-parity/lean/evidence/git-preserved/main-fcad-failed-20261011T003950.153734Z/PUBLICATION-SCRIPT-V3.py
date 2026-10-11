"""Publish one frozen evidence export without materializing a second local copy."""
import datetime
import hashlib
import json
import os
import pathlib
import subprocess

REPO = pathlib.Path('/workspace/Research-Commons')
PACKET = REPO / 'research/2026-10-10-codex-lean-rust-parity'
RESULT = PACKET / 'lean/G6-NATURAL-COMMON-FACTORIZATION-MAIN-FCAD-FAILED-20261011T003950.153734Z-RESULT.json'
RESULT_SHA = '1939fe2afec3c55f50406556c07a9181acb44881091897659bb1962803f6c83b'
EXPORT = pathlib.Path('/dev/shm/rc-lean-g6-natural-common-20261011T003502.004915Z/lossless-export/main-fcad-failed-20261011T003950.153734Z')
PREFIX = 'research/2026-10-10-codex-lean-rust-parity/lean/evidence/git-preserved/main-fcad-failed-20261011T003950.153734Z'
OBJECTS = pathlib.Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z')
INDEX = pathlib.Path('/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT')
OUT = pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication/PUBLICATION-V3.json')
ENV = {**os.environ, 'GIT_OBJECT_DIRECTORY': str(OBJECTS),
       'GIT_ALTERNATE_OBJECT_DIRECTORIES': str(REPO / '.git/objects'),
       'GIT_INDEX_FILE': str(INDEX), 'GIT_OPTIONAL_LOCKS': '0'}


def git(*args, data=None):
    return subprocess.check_output(['git', *args], input=data, cwd=REPO, env=ENV)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def size(root):
    return sum(p.stat().st_size for p in root.rglob('*') if p.is_file())


def free(path):
    s = os.statvfs(path)
    return s.f_bavail * s.f_frsize


def main():
    assert not OUT.exists()
    result_bytes = RESULT.read_bytes()
    assert digest(result_bytes) == RESULT_SHA
    result = json.loads(result_bytes)
    assert result['complete_lossless_export_original'] == str(EXPORT)
    assert result['packet_distribution_complete'] is False
    assert (EXPORT / 'PRESERVATION-MANIFEST.json').read_bytes() == result_bytes
    for row in result['preserved_files']:
        data = (EXPORT / row['path']).read_bytes()
        assert digest(data) == row['sha256'] and len(data) == row['bytes']
    rows = []
    for path in sorted(EXPORT.rglob('*')):
        assert not path.is_symlink()
        if not path.is_file():
            continue
        data = path.read_bytes()
        rel = str(path.relative_to(EXPORT))
        target = PREFIX + '/' + rel
        assert not (REPO / target).exists()
        assert not git('ls-files', '--stage', '--', target).strip()
        blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        rows.append({'original_path': str(path), 'git_tree_path': target,
                     'sha256': digest(data), 'bytes': len(data), 'git_blob': blob})
    assert len(rows) == 57
    payload = sum(row['bytes'] for row in rows)
    before = {'object_pool_bytes': size(OBJECTS), 'tmp_free_bytes': free('/tmp'),
              'overlay_free_bytes': free('/workspace'), 'index_bytes': INDEX.stat().st_size}
    # An object per file can be no larger than its input plus this conservative allowance.
    assert before['object_pool_bytes'] + payload + len(rows) * 4096 < 64 * 1024 * 1024
    assert before['tmp_free_bytes'] > payload + len(rows) * 4096 + before['index_bytes'] + 2 * 1024 * 1024
    assert before['overlay_free_bytes'] > 8 * 1024 * 1024
    preexisting = git('ls-files', '--stage', '-z')
    for row in rows:
        data = pathlib.Path(row['original_path']).read_bytes()
        assert digest(data) == row['sha256'] and len(data) == row['bytes']
        blob = git('hash-object', '-w', '--stdin', data=data).decode().strip()
        assert blob == row['git_blob']
        assert git('cat-file', 'blob', blob) == data
    additions = b''.join(('100644 ' + row['git_blob'] + '\t' + row['git_tree_path'] + '\0').encode() for row in rows)
    git('update-index', '-z', '--index-info', data=additions)
    git('update-index', '--skip-worktree', '--', *(row['git_tree_path'] for row in rows))
    current = git('ls-files', '--stage', '-z')
    new_paths = {row['git_tree_path'].encode() for row in rows}
    filtered = b''.join(record + b'\0' for record in current.split(b'\0') if record and record.split(b'\t', 1)[1] not in new_paths)
    assert filtered == preexisting
    for row in rows:
        status = git('ls-files', '-v', '--', row['git_tree_path']).decode()
        assert status.startswith('S ')
        assert git('show', ':' + row['git_tree_path']) == pathlib.Path(row['original_path']).read_bytes()
    after = {'object_pool_bytes': size(OBJECTS), 'tmp_free_bytes': free('/tmp'),
             'overlay_free_bytes': free('/workspace'), 'index_bytes': INDEX.stat().st_size}
    assert after['object_pool_bytes'] < 64 * 1024 * 1024
    assert after['overlay_free_bytes'] > 8 * 1024 * 1024
    receipt = {
        'status': 'INDEXED_COMPLETE_EXPORT_BYTES_WITH_EXPLICIT_LOCAL_SPARSE_MATERIALIZATION',
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'original_result_path': str(RESULT), 'original_result_sha256': RESULT_SHA,
        'original_result_unchanged': True, 'original_packet_distribution_complete': False,
        'export': str(EXPORT), 'files': rows, 'files_count': len(rows), 'payload_bytes': payload,
        'preexisting_index_entries_identical': True, 'every_blob_byte_readback': True,
        'working_tree_materialized': False, 'only_new_evidence_paths_skip_worktree': True,
        'existing_files_deleted_or_hidden': False, 'scientific_acceptance_promoted': False,
        'before': before, 'after': after,
        'publication_scope': 'All bytes of this frozen export are indexed for the next commit; commit and remote push are separate later checks. Local originals remain at the bound fixed-shmem path. The old capacity-boundary receipt remains unchanged.',
    }
    OUT.write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    assert free('/workspace') > 8 * 1024 * 1024
    print(json.dumps({'receipt': str(OUT), 'sha256': digest(OUT.read_bytes()), 'files': len(rows), 'payload_bytes': payload}))


if __name__ == '__main__':
    main()
