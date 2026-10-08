"""Read-only Git Blobs API retrieval of Dot's exact34-file frozen allowlist."""
import argparse
import base64
import concurrent.futures
import hashlib
import json
import re
import subprocess
from pathlib import Path, PurePosixPath

NOTE = 'handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/inbox/G6/20261007T234400Z-DOT-RUST-CODEX-OWNERSHIP-TRANSFER.md'
NOTE_SHA = '59a59be2289e679ee0aaa020ffd6d2a8114b803ca2b43347ee5faf31656fcb43'
PREFIX = 'research/2026-10-07-rust-count-pilot'


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def git_blob(raw):
    return hashlib.sha1(b'blob ' + str(len(raw)).encode('ascii') + b'\0' + raw).hexdigest()


def retrieve(root, receipt):
    note = (root / NOTE).read_bytes()
    if digest(note) != NOTE_SHA:
        raise ValueError('ownership-transfer note identity')
    match = re.search(r'```json\n(.*?)\n```', note.decode('utf-8'), re.S)
    manifest = json.loads(match.group(1))
    if (manifest['schema'] != 'rust-count-pilot-cloud-transfer-v1' or
            manifest['repository'] != 'Sodelin/Research-Commons' or manifest['prefix'] != PREFIX or
            manifest['file_count'] != 34 or len(manifest['files']) != 34 or
            manifest['total_bytes'] != 1225944 or sum(row['bytes'] for row in manifest['files']) != 1225944):
        raise ValueError('exact transfer manifest identity/count/size')
    paths = set()
    for row in manifest['files']:
        path = PurePosixPath(row['path'])
        if (path.is_absolute() or '..' in path.parts or not path.parts or
                str(path) != row['path'] or row['path'] in paths or
                not re.fullmatch('[0-9a-f]{40}', row['git_blob_sha']) or
                not re.fullmatch('[0-9a-f]{64}', row['sha256'])):
            raise ValueError('unsafe/duplicate manifest entry')
        paths.add(row['path'])
    destination = root / PREFIX
    if destination.exists() or destination.is_symlink() or receipt.exists():
        raise ValueError('refuse existing pilot prefix/receipt; inspect concurrent publication')

    def fetch(row):
        endpoint = 'repos/Sodelin/Research-Commons/git/blobs/' + row['git_blob_sha']
        run = subprocess.run(['gh', 'api', endpoint], capture_output=True, timeout=30, check=True)
        response = json.loads(run.stdout)
        if response['encoding'] != 'base64':
            raise ValueError('unexpected blob encoding')
        body = base64.b64decode(response['content'])
        body.decode('utf-8')  # Validate the transferred UTF-8 constraint; retain exact bytes.
        if (response['sha'] != row['git_blob_sha'] or response['size'] != row['bytes'] or
                len(body) != row['bytes'] or digest(body) != row['sha256'] or git_blob(body) != row['git_blob_sha']):
            raise ValueError('blob identity/length/SHA mismatch: ' + row['path'])
        return row, body

    # Independent read-only blob requests; preserve all payloads only after all
    #34 identities pass. No tree/ref mutation or supplied code is executed here.
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        verified = list(pool.map(fetch, manifest['files']))
    destination.mkdir(parents=True, exist_ok=False)
    rows = []
    for row, body in verified:
        target = destination / row['path']; target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as out:
            out.write(body)
        target.chmod(0o644)
        if target.read_bytes() != body:
            raise ValueError('local destination readback mismatch')
        rows.append(dict(row, git_blob_sha_verified=True, sha256_verified=True,
                         utf8_verified=True, file_mode='100644'))
    actual = {str(f.relative_to(destination)) for f in destination.rglob('*') if f.is_file()}
    if actual != paths:
        raise ValueError('destination is not exactly the34-file allowlist')
    result = {'schema': 'cloud_dot_native_rust_transfer_retrieval_v1', 'contributor': 'Dot',
              'retriever_publisher': 'Codex Cloud practical lane', 'ownership_note': NOTE,
              'ownership_note_sha256': NOTE_SHA, 'prefix': PREFIX, 'file_count': len(rows),
              'total_bytes': sum(row['bytes'] for row in rows), 'files': rows,
              'historical_manifests_and_results_unchanged': True,
              'api_route': 'GET /repos/Sodelin/Research-Commons/git/blobs/{sha}',
              'no_binaries_toolchains_or_new_numerical_runs': True}
    with receipt.open('x') as out:
        json.dump(result, out, indent=2, sort_keys=True); out.write('\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--commons-root', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    result = retrieve(args.commons_root.resolve(), args.receipt.absolute())
    print(json.dumps({'status': 'EXACT34_RETRIEVED', 'files': result['file_count'],
                      'bytes': result['total_bytes'], 'prefix': result['prefix']}, sort_keys=True))
