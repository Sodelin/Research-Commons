"""Read-only, dated saved-byte review; never relocates, updates Git, or builds."""
from pathlib import Path, PurePosixPath
import datetime
import hashlib
import json
import os
import subprocess

REPO = Path('/workspace/Research-Commons')
W = Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
B = W / 'metadata/git-evidence-publication'
ENV = dict(os.environ, GIT_OPTIONAL_LOCKS='0')
PINS = {
    'GIT-OBJECT-POOL-LOSSLESS-RELOCATION-20261011.json': 'c51fd70115ddc541c8f57a022ad7970be8fb322091b26b5adb6561e7fa43b941',
    'ROOT-GIT-OBJECT-POOL-SAVED-READBACK-20261011T0139Z.json': '7bf7cb7be42823d582612eca77b85e960434016549748101ed37feccdacc93e0',
    'NATURAL-5F-FAILURE-PUBLICATION.json': '91c3398ff7cb9167d4efacdcd835da5ab831ad5f17a165c624d675fb6ed642d3',
    'PRIVATE-SELECTED-PREFIX-PUBLICATION-20261011T0136Z.json': '61defdc7615c744da487f12c47528d49f9bb070ea7850866d0ac40107f3d874a',
    'RUST-INDEPENDENT-OBJECT-POOL-SAVED-READER-ATTEMPT1-FAILURE-20261011T0146Z.json': '926e4e89a45a613e0bdc32ea84b496fbd8588799f8e0ccc9c9e573af58cc782b',
    'RUST-INDEPENDENT-OBJECT-POOL-V2-SOURCE-QC-20261011T013827Z.json': '934d0334b56a050e194f9e7b0fa2507018c1ed61145a053282f1e893d6aca57c',
}
FOREST = 'research/2026-10-10-codex-lean-rust-parity/lean/evidence/git-preserved/forest101-pass-20261011T005209.997288Z/'
ACCEPTED = 'research/2026-10-10-codex-lean-rust-parity/lean/G6-FOREST-REGISTER-COMPRESSION-101-ACCEPTANCE-20261011T0109Z.json'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def pin(path):
    path = Path(path)
    h = hashlib.sha256()
    total = 0
    with path.open('rb') as stream:
        while piece := stream.read(65536):
            h.update(piece)
            total += len(piece)
    return {'path': str(path), 'bytes': total, 'sha256': h.hexdigest()}


def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args], env=ENV)


def inventory_paths(root):
    paths = sorted(root.rglob('*'))
    require(not any(p.is_symlink() for p in paths), 'Unexpected symlink inside preserved pool')
    return [str(p.relative_to(root)) for p in paths if p.is_file()]


def review():
    started = datetime.datetime.now(datetime.timezone.utc).isoformat()
    bindings = {}
    for name, expected in PINS.items():
        item = pin(B / name)
        require(item['sha256'] == expected, 'Input pin changed: ' + name)
        bindings[name] = item
    relocation = json.loads((B / 'GIT-OBJECT-POOL-LOSSLESS-RELOCATION-20261011.json').read_bytes())
    prior = json.loads((B / 'ROOT-GIT-OBJECT-POOL-SAVED-READBACK-20261011T0139Z.json').read_bytes())
    pub_names = ['NATURAL-5F-FAILURE-PUBLICATION.json', 'PRIVATE-SELECTED-PREFIX-PUBLICATION-20261011T0136Z.json']
    publications = [json.loads((B / name).read_bytes()) for name in pub_names]
    original_publication_path = B / 'FOREST101-PUBLICATION.json'
    original_publication = json.loads(original_publication_path.read_bytes())
    bindings['FOREST101-PUBLICATION.json'] = pin(original_publication_path)
    require(relocation['objects_count'] == len(relocation['rows']) == 2261, 'Snapshot count mismatch')
    require(relocation['status'] == 'FULL_GIT_OBJECT_POOL_RELOCATED_WITH_IDENTICAL_LOGICAL_BYTES', 'Snapshot status mismatch')
    old = Path(relocation['old_logical_path'])
    new = Path(relocation['counted_preserved_path'])
    backup = Path('/tmp/rc-cloud-git-objects-verified-redirect-backup-20261011')
    require(old.is_symlink() and old.resolve() == new, 'Logical object redirect mismatch')
    require(new.is_dir() and not new.is_symlink(), 'Counted pool is not a literal directory')
    require(not backup.exists() and not backup.is_symlink(), 'Verified redirect backup still present')
    alternates_path = REPO / '.git/objects/info/alternates'
    require(alternates_path.read_bytes() == (str(old) + '\n').encode(), 'Git alternates mismatch')
    bindings['git_alternates'] = pin(alternates_path)
    inventory_before = inventory_paths(new)
    snapshot_by_name = {x['path']: x for x in relocation['rows']}
    require(len(snapshot_by_name) == 2261 and set(snapshot_by_name).issubset(inventory_before), 'Snapshot is not retained')
    object_rows = []
    for name in inventory_before:
        relative = PurePosixPath(name)
        require(not relative.is_absolute() and '..' not in relative.parts, 'Unsafe relative object name')
        logical = pin(old / name)
        counted = pin(new / name)
        require(logical['bytes'] == counted['bytes'] and logical['sha256'] == counted['sha256'], 'Logical/counting bytes differ: ' + name)
        saved = snapshot_by_name.get(name)
        if saved:
            require(counted['bytes'] == saved['bytes'] and counted['sha256'] == saved['sha256'], 'Saved object changed: ' + name)
        object_rows.append({'path': name, 'bytes': counted['bytes'], 'logical_sha256': logical['sha256'], 'counted_sha256': counted['sha256'], 'present_in_original_2261_snapshot': saved is not None})
    current_pool_bytes = sum(x['bytes'] for x in object_rows)
    require(current_pool_bytes <= 67108864, 'Current pool exceeds recorded 64MiB cap')
    head_before = git('rev-parse', '--verify', 'HEAD').decode().strip()
    require(head_before == prior['head'], 'HEAD changed since dated root readback')
    index_path = REPO / '.git/index'
    index_before = pin(index_path)
    raw = git('ls-files', '--stage', '-z')
    new_by_name = {}
    for publication, expected_count in zip(publications, [53, 87]):
        require(publication['files_count'] == len(publication['files']) == expected_count, 'Publication count mismatch')
        require(publication['preexisting_index_entries_identical'] is True, 'Publisher retention observation missing')
        for item in publication['files']:
            name = item['git_tree_path']
            require(name not in new_by_name, 'Duplicate new publication path')
            new_by_name[name] = item
    require(len(new_by_name) == 140, 'Expected 140 explicit new paths')
    retained_hash = hashlib.sha256()
    indexed = {}
    count_before_extensions = 0
    for record in raw.split(b'\0'):
        if not record:
            continue
        fields, path_bytes = record.split(b'\t', 1)
        mode, oid, stage = fields.split()
        name = path_bytes.decode()
        require(name not in indexed, 'Duplicate staged path')
        indexed[name] = {'git_tree_path': name, 'mode': mode.decode(), 'git_blob': oid.decode(), 'stage': int(stage)}
        if name not in new_by_name:
            retained_hash.update(record + b'\0')
            count_before_extensions += 1
    require(retained_hash.hexdigest() == prior['indexed_entries_sha256'], 'Pre-existing staged entries changed')
    require(set(new_by_name).issubset(indexed), 'A published new path is absent')
    require(len(indexed) == count_before_extensions + 140 == 101275, 'Current staged count mismatch')
    require(index_before['bytes'] == publications[-1]['after']['index_bytes'], 'Current index size differs from final publication observation')
    forest_rows = [x for name, x in indexed.items() if name.startswith(FOREST)]
    require(len(forest_rows) == prior['forest_indexed_regular_files'] == 72, 'Forest export-prefix count changed')
    require(ACCEPTED in indexed, 'Accepted forest JSON is not indexed')
    expected_blobs = {x['git_tree_path']: x for x in original_publication['files']}
    require(len(expected_blobs) == 66, 'Original forest export count mismatch')
    expected_blobs.update(new_by_name)
    selected = list(forest_rows) + [indexed[name] for name in new_by_name] + [indexed[ACCEPTED]]
    require(len(selected) == 213 and len({x['git_tree_path'] for x in selected}) == 213, 'Readback selection mismatch')
    batch = subprocess.Popen(['git', '-C', str(REPO), 'cat-file', '--batch'], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, env=ENV)
    try:
        batch.stdin.write((''.join(x['git_blob'] + '\n' for x in selected)).encode())
        batch.stdin.close()
        for row in selected:
            require(row['mode'] == '100644' and row['stage'] == 0, 'Unexpected staged mode/stage')
            header = batch.stdout.readline().decode().strip().split()
            require(len(header) == 3 and header[0] == row['git_blob'] and header[1] == 'blob', 'Git blob header mismatch')
            size = int(header[2])
            remaining = size
            sha256 = hashlib.sha256()
            git_sha1 = hashlib.sha1(('blob ' + str(size) + '\0').encode())
            first = b''
            while remaining:
                piece = batch.stdout.read(min(remaining, 65536))
                require(bool(piece), 'Truncated Git blob')
                remaining -= len(piece)
                sha256.update(piece)
                git_sha1.update(piece)
                if not first:
                    first = piece[:8]
            require(batch.stdout.read(1) == b'\n', 'Missing blob separator')
            require(git_sha1.hexdigest() == row['git_blob'], 'Git object content hash mismatch')
            require(not first.startswith(b'\x7fELF'), 'Compiled ELF found in selected text publication')
            row.update({'bytes': size, 'sha256': sha256.hexdigest(), 'git_blob_content_hash_verified': True, 'compiled_ELF_magic_present': False})
            expected = expected_blobs.get(row['git_tree_path'])
            if expected:
                require(row['git_blob'] == expected['git_blob'] and size == expected['bytes'] and row['sha256'] == expected['sha256'], 'Published blob differs from receipt')
                original = pin(expected['original_path'])
                require(original['bytes'] == size and original['sha256'] == row['sha256'], 'Retained original differs from published blob')
                row['retained_original'] = original
            if row['git_tree_path'] == ACCEPTED:
                require(row['sha256'] == prior['accepted_forest_blob_readback_sha256'], 'Accepted forest JSON readback changed')
                source = pin(REPO / ACCEPTED)
                require(source['bytes'] == size and source['sha256'] == row['sha256'], 'Accepted forest working file changed')
                row['retained_original'] = source
        stderr = batch.stderr.read()
        require(batch.wait() == 0 and stderr == b'', 'Read-only Git batch failed')
    finally:
        if batch.poll() is None:
            batch.kill()
            batch.wait()
        for stream in [batch.stdout, batch.stderr]:
            stream.close()
    head_after = git('rev-parse', '--verify', 'HEAD').decode().strip()
    index_after = pin(index_path)
    stages_after = git('ls-files', '--stage', '-z')
    require(head_after == head_before and index_after == index_before and stages_after == raw, 'Concurrent Git state change during review')
    require(inventory_paths(new) == inventory_before and old.is_symlink() and old.resolve() == new, 'Object namespace changed during review')
    return {
        'schema': 'research_commons_dated_saved_object_pool_review_v2',
        'reader': '/root/rust_implementation',
        'status': 'PASS_SAVED_RELOCATION_BYTES_RETAINED_WITH_AUTHENTICATED_LATER_PUBLICATION_EXTENSION',
        'started_utc': started,
        'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'source': pin(__file__),
        'input_bindings': bindings,
        'logical_pool_path': str(old),
        'counted_pool_path': str(new),
        'logical_pool_is_symlink_to_counted_literal_directory': True,
        'verified_redirect_backup_absent': True,
        'saved_original_objects_checked_at_both_paths': 2261,
        'current_pool_regular_files': len(object_rows),
        'current_pool_bytes': current_pool_bytes,
        'current_pool_cap_bytes': 67108864,
        'saved_original_content_bytes': sum(x['bytes'] for x in relocation['rows']),
        'current_additional_object_count': len(object_rows) - 2261,
        'object_rows': object_rows,
        'head_before_after': head_before,
        'current_index_before_after': index_before,
        'current_index_logical_symlink': str(index_path),
        'current_index_resolved_path': str(index_path.resolve()),
        'relocation_time_index_bytes': prior['index_bytes'],
        'relocation_time_index_sha256': prior['index_sha256'],
        'current_index_bytes_equal_to_relocation_time': index_before['bytes'] == prior['index_bytes'],
        'dated_index_change_explained_by_exact_publication_paths': 140,
        'retained_original_stage_entries': count_before_extensions,
        'retained_original_stage_listing_sha256': retained_hash.hexdigest(),
        'current_stage_entries': len(indexed),
        'current_stage_listing_bytes': len(raw),
        'current_stage_listing_sha256': hashlib.sha256(raw).hexdigest(),
        'forest_export_blobs_read': 72,
        'original_forest_export_blobs_compared_to_retained_files': 66,
        'later_publication_blobs_compared_to_retained_files': 140,
        'accepted_forest_json_separately_read': ACCEPTED,
        'git_blob_rows': selected,
        'read_only_git_subcommands': ['rev-parse --verify HEAD', 'ls-files --stage -z', 'cat-file --batch'],
        'git_optional_locks': '0',
        'relocation_rerun': False,
        'git_mutations': False,
        'scientific_or_accepted_source_edits': False,
        'compiler_native_reference_or_mathematical_producers_started': False,
        'compiled_ELF_or_old_evidence_removed_or_copied': False,
        'all_reader_outputs_in_existing_counted_forest_metadata': True,
        'qualification': 'Dated readback of the normal completed relocation and later authorized publications. This does not establish crash atomicity, future Git-writer safety, mathematical acceptance, or public/native refinement. Root relocation-time index identity is preserved as an exact filtered stage-list subset, not claimed to equal the extended current index bytes.',
    }


if __name__ == '__main__':
    result = review()
    path = B / 'RUST-INDEPENDENT-OBJECT-POOL-SAVED-QC-V2-20261011T0150Z.json'
    raw = (json.dumps(result, sort_keys=True, indent=2) + '\n').encode()
    with path.open('xb') as stream:
        stream.write(raw)
    print(json.dumps({'path': str(path), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(), 'status': result['status'], 'saved_objects': result['saved_original_objects_checked_at_both_paths'], 'current_objects': result['current_pool_regular_files'], 'current_pool_bytes': result['current_pool_bytes'], 'readback_blobs': len(result['git_blob_rows']), 'retained_entries': result['retained_original_stage_entries'], 'new_entries': result['dated_index_change_explained_by_exact_publication_paths']}, sort_keys=True))
