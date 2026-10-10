#!/usr/bin/env python3
"""Account for all published paths since this task's initial Commons snapshot.

File inventory completeness is scoped to an exact Git range. It is not a claim
that every historical mathematical argument has been independently reviewed.
"""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess

PACKET = Path(__file__).resolve().parents[1]
ROOT = PACKET.parents[1]
BASE = 'c5fec79ddf742f6b2153aaa20d46c7e869048844'


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT)


def main():
    snapshot = git('rev-parse', 'origin/main').decode().strip()
    paths = git('diff', '--name-only', '-z', BASE, snapshot).decode().split('\0')[:-1]
    tree = {}
    for entry in git('ls-tree', '-r', '-z', '--long', snapshot).split(b'\0'):
        if entry:
            meta, name = entry.split(b'\t', 1)
            mode, kind, blob, size = meta.decode().split()
            tree[name.decode()] = (mode, kind, blob, int(size))
    files, errors = [], []
    for relative in paths:
        mode, kind, blob, size = tree[relative]
        path = ROOT / relative
        if kind != 'blob' or mode not in ('100644', '100755') or path.is_symlink() or not path.is_file():
            errors.append(relative)
            continue
        raw = path.read_bytes()
        observed_blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if len(raw) != size or observed_blob != blob:
            errors.append(relative)
        files.append({'path': relative, 'bytes': len(raw), 'git_blob': blob,
                      'sha256': hashlib.sha256(raw).hexdigest()})
    commits = []
    for line in git('log', '--reverse', '--format=%H%x09%aI%x09%s', BASE + '..' + snapshot).decode().splitlines():
        commit, date, subject = line.split('\t', 2)
        commits.append({'commit': commit, 'authored': date, 'subject': subject})
    groups = Counter('/'.join(p.split('/')[:2]) for p in paths)
    g34 = sorted(key for key in groups if key.startswith('research/2026-10-10-dot-g3-')
                 or key.startswith('research/2026-10-10-dot-g4-'))
    index = PACKET / 'design/DISCOVERY-MAP.md'
    text = index.read_text()
    missing = [key for key in g34 if Path(key).name not in text]
    errors += ['Discovery index omits ' + key for key in missing]
    receipt = {
        'schema': 'recent_commons_publication_coverage_v1',
        'status': 'ALL_RECENT_PUBLISHED_PATHS_ACCOUNTED_FOR' if not errors else 'FAIL',
        'observed_utc': datetime.now(timezone.utc).isoformat(),
        'range_start': BASE, 'published_snapshot': snapshot,
        'commits': commits, 'changed_path_count': len(paths),
        'groups': dict(sorted(groups.items())), 'g3_g4_packet_count': len(g34),
        'g3_g4_packets': g34,
        'compact_index': {'path': str(index.relative_to(ROOT)),
                          'sha256': hashlib.sha256(index.read_bytes()).hexdigest(),
                          'all_recent_g3_g4_packets_linked': not missing},
        'files': files, 'errors': errors,
        'coverage_boundary': {
            'all_paths_in_recorded_publication_range_inventoried': not errors,
            'local_bytes_match_published_git_blobs': not errors,
            'recent_g3_g4_claims_and_reviews_indexed': not missing,
            'every_historical_commons_proof_reread': False,
            'every_new_hand_proof_independently_reproved': False,
            'all_new_results_formalized_or_executed': False,
        },
        'scope': 'Publication discovery and exact source identity for the recorded range, plus compact G3/G4 index coverage. Build, proof review, source admission and execution have separate receipts.',
        'reviewer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    (PACKET / 'quality/RECENT-PUBLICATION-COVERAGE.json').write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'status': receipt['status'], 'commits': len(commits),
                      'changed_paths': len(paths), 'g3_g4_packets': len(g34), 'errors': errors}))
    return bool(errors)


if __name__ == '__main__':
    raise SystemExit(main())
