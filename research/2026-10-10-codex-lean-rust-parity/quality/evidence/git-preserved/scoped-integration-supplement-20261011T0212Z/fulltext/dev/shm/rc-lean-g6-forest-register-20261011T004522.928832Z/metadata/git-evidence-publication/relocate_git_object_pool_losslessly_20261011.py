"""Relocate the fixed Git object pool with identical bytes and logical paths.

No source, compiler artifact, attempt, receipt, index, or Git reference changes.
The 64 MiB object cap and existing counted-resource limits remain unchanged.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil

WORK = Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
OLD = Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z')
NEW = WORK / 'metadata/git-object-pool-preserved-20261011'
BACKUP = Path('/tmp/rc-cloud-git-objects-verified-redirect-backup-20261011')
PLAN = Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z/RESOURCE-AND-RUN-PLAN.json')
PLAN_SHA = '0db1bb265fec8e2a4c89b0361d2b48f3f38c17d35aeb479b623c0954f097bac5'
OUT = WORK / 'metadata/git-evidence-publication/GIT-OBJECT-POOL-LOSSLESS-RELOCATION-20261011.json'
OBJECT_CAP = 64 * 1024 * 1024
SCRATCH_ABORT = 2013265920
MEMORY_ABORT = 16106127360
NEXT_PROOF_RESERVE = 79691776


def digest(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        while piece := stream.read(65536):
            h.update(piece)
    return h.hexdigest()


def inventory(root):
    rows = []
    for p in sorted(root.rglob('*')):
        assert not p.is_symlink()
        if p.is_file():
            st = p.stat()
            rows.append({'path': str(p.relative_to(root)), 'bytes': st.st_size,
                         'allocated_bytes': st.st_blocks * 512, 'sha256': digest(p)})
        else:
            assert p.is_dir()
    return rows


def measured(roots):
    seen = set()
    total = 0
    for root in roots:
        assert Path(root).is_dir()
        for directory, dirs, files in os.walk(root, followlinks=False):
            for p in [Path(directory), *(Path(directory) / name for name in files)]:
                st = p.lstat()
                key = (st.st_dev, st.st_ino)
                if key not in seen:
                    seen.add(key)
                    total += st.st_blocks * 512
    values = dict(line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
    memory = sum(int(values[k]) for k in ('anon', 'shmem', 'kernel'))
    return {'scratch_bytes': total, 'nonreclaim_bytes': memory}


def check_limits(roots):
    actual = measured(roots)
    assert actual['scratch_bytes'] < SCRATCH_ABORT
    assert actual['nonreclaim_bytes'] < MEMORY_ABORT
    return actual


def main():
    assert OLD.is_dir() and not OLD.is_symlink()
    assert not NEW.exists() and not BACKUP.exists() and not OUT.exists()
    assert digest(PLAN) == PLAN_SHA
    plan = json.loads(PLAN.read_bytes())
    roots = plan['allocation_roots']
    assert len(roots) == 25 and str(WORK) in roots
    assert plan['scratch_abort_bytes'] == SCRATCH_ABORT
    assert plan['scratch_hard_limit_bytes'] == 2147483648
    assert plan['memory_abort_bytes'] == MEMORY_ABORT
    assert not any((Path(r) / 'ACTIVE-GUARDED-PROCESS.json').exists() for r in roots)
    before = check_limits(roots)
    rows = inventory(OLD)
    payload = sum(r['bytes'] for r in rows)
    assert payload < OBJECT_CAP
    # New files plus every original directory and conservative block slack.
    reserve = sum(r['allocated_bytes'] for r in rows) + (len(rows) + 512) * 4096
    assert before['scratch_bytes'] + reserve + NEXT_PROOF_RESERVE < SCRATCH_ABORT
    assert before['nonreclaim_bytes'] + reserve < MEMORY_ABORT
    tmp_before = os.statvfs('/tmp').f_bavail * os.statvfs('/tmp').f_frsize
    NEW.mkdir()
    for i, row in enumerate(rows):
        source, dest = OLD / row['path'], NEW / row['path']
        assert digest(source) == row['sha256']
        dest.parent.mkdir(parents=True, exist_ok=True)
        with source.open('rb') as incoming, dest.open('xb') as outgoing:
            shutil.copyfileobj(incoming, outgoing, 65536)
            outgoing.flush()
            os.fsync(outgoing.fileno())
        shutil.copystat(source, dest)
        assert digest(dest) == row['sha256'] and dest.stat().st_size == row['bytes']
        if i % 64 == 0:
            check_limits(roots)
    assert inventory(OLD) == rows
    copied = inventory(NEW)
    assert [(r['path'], r['bytes'], r['sha256']) for r in copied] == [(r['path'], r['bytes'], r['sha256']) for r in rows]
    check_limits(roots)
    OLD.rename(BACKUP)
    OLD.symlink_to(NEW, target_is_directory=True)
    # Every original logical object path resolves to the exact retained bytes.
    for row in rows:
        assert digest(OLD / row['path']) == row['sha256']
        assert digest(BACKUP / row['path']) == row['sha256']
    assert inventory(NEW) == copied
    # Remove only the redundant temporary directory after both exact rehashes.
    # All object content remains at its original logical path and counted target.
    shutil.rmtree(BACKUP)
    assert OLD.resolve() == NEW and not BACKUP.exists()
    after = check_limits(roots)
    assert after['scratch_bytes'] + NEXT_PROOF_RESERVE < SCRATCH_ABORT
    report = {'status': 'FULL_GIT_OBJECT_POOL_RELOCATED_WITH_IDENTICAL_LOGICAL_BYTES',
              'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'old_logical_path': str(OLD), 'counted_preserved_path': str(NEW),
              'object_cap_bytes_unchanged': OBJECT_CAP, 'content_bytes': payload,
              'objects_count': len(rows), 'before': before, 'after': after,
              'tmp_free_before': tmp_before,
              'tmp_free_after': os.statvfs('/tmp').f_bavail * os.statvfs('/tmp').f_frsize,
              'source_cache_attempt_receipt_index_reference_changes': False,
              'logical_object_bytes_changed': False, 'rows': rows}
    with OUT.open('x') as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write('\n')
    print(json.dumps({'receipt': str(OUT), 'sha256': digest(OUT), 'objects_count': len(rows),
                      'tmp_free_after': report['tmp_free_after'], 'after': after}))


if __name__ == '__main__':
    main()
