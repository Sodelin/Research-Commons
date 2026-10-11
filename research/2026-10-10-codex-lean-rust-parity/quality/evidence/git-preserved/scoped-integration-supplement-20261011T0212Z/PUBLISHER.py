"""Preserve full frozen text evidence through regular Git blobs, without another file copy."""
import datetime
import hashlib
import json
import os
import pathlib
import subprocess

REPO = pathlib.Path('/workspace/Research-Commons')
BASE = pathlib.Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/git-evidence-publication')
MANIFEST = BASE / 'SUPPLEMENTAL-PUBLICATION-INPUTS-V2.json'
MANIFEST_SHA = 'bbb443e9fbfb61a157b6dc24d5d0995791fb562b9381a41e7bb886ce72cab26c'
OUT = BASE / 'FULL-SCOPED-SUPPLEMENT-PUBLICATION.json'
OBJECTS = pathlib.Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z')
INDEX = pathlib.Path('/tmp/rc-cloud-git-index-20261010T224217.512566Z/INDEX-CURRENT')
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
    manifest_data = MANIFEST.read_bytes()
    assert digest(manifest_data) == MANIFEST_SHA
    plan = json.loads(manifest_data)
    assert plan['files_count'] == 118
    rows = [dict(row) for row in plan['files']]
    for name, path in [('INPUT-MANIFEST.json', MANIFEST), ('PUBLISHER.py', pathlib.Path(__file__))]:
        data = path.read_bytes()
        rows.append({'source_path': str(path), 'git_tree_path': plan['prefix'] + '/' + name,
                     'bytes': len(data), 'sha256': digest(data)})
    assert len(rows) == 120
    assert len({row['git_tree_path'] for row in rows}) == len(rows)
    for row in rows:
        source = pathlib.Path(row['source_path'])
        assert source.is_file() and not source.is_symlink()
        data = source.read_bytes()
        data.decode('utf-8')
        assert not data.startswith(b'\x7fELF')
        assert digest(data) == row['sha256'] and len(data) == row['bytes']
        assert not (REPO / row['git_tree_path']).exists()
        assert not git('ls-files', '--stage', '--', row['git_tree_path']).strip()
        row['git_blob'] = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    payload = sum(row['bytes'] for row in rows)
    assert payload < 8 * 1024 * 1024
    before = {'object_pool_bytes': size(OBJECTS), 'tmp_free_bytes': free('/tmp'),
              'overlay_free_bytes': free('/workspace'), 'index_bytes': INDEX.stat().st_size}
    assert before['object_pool_bytes'] + payload + len(rows) * 4096 < 96 * 1024 * 1024
    assert before['tmp_free_bytes'] > payload + len(rows) * 4096 + before['index_bytes'] + 2 * 1024 * 1024
    assert before['overlay_free_bytes'] > 8 * 1024 * 1024
    preexisting = git('ls-files', '--stage', '-z')
    for row in rows:
        data = pathlib.Path(row['source_path']).read_bytes()
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
        assert git('ls-files', '-v', '--', row['git_tree_path']).decode().startswith('S ')
        assert git('show', ':' + row['git_tree_path']) == pathlib.Path(row['source_path']).read_bytes()
    after = {'object_pool_bytes': size(OBJECTS), 'tmp_free_bytes': free('/tmp'),
             'overlay_free_bytes': free('/workspace'), 'index_bytes': INDEX.stat().st_size}
    assert after['object_pool_bytes'] < 96 * 1024 * 1024
    assert after['overlay_free_bytes'] > 8 * 1024 * 1024
    receipt = {'status': 'INDEXED_FULL_FROZEN_TEXT_BYTES_WITH_EXPLICIT_LOCAL_SPARSE_MATERIALIZATION',
               'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'input_manifest_path': str(MANIFEST), 'input_manifest_sha256': MANIFEST_SHA,
               'files': rows, 'files_count': len(rows), 'payload_bytes': payload,
               'preexisting_index_entries_identical': True, 'every_blob_byte_readback': True,
               'working_tree_materialized': False, 'only_new_evidence_paths_skip_worktree': True,
               'existing_files_deleted_or_hidden': False, 'scientific_acceptance_promoted': False,
               'before': before, 'after': after, 'remote_commit_push_pending': True}
    OUT.write_text(json.dumps(receipt, sort_keys=True, indent=2) + '\n')
    print(json.dumps({'receipt': str(OUT), 'sha256': digest(OUT.read_bytes()),
                      'files': len(rows), 'payload_bytes': payload}))


if __name__ == '__main__':
    main()
