#!/usr/bin/env python3
"""Source/bytes-only gate; does not run Git or import the publisher."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
SOURCE = P / 'quality/publish_fixed_shmem_evidence_to_git_20261011.py'
SOURCE_SHA = 'f849de01ded015872d3c555999f4ae24a7e3563bc28a09731a13bb25ac348d9a'
E = Path('/dev/shm/rc-lean-g6-natural-common-20261011T003502.004915Z/lossless-export/main-fcad-failed-20261011T003950.153734Z')


def demand(ok, why):
    if not ok:
        raise AssertionError(why)


def sha(b):
    return hashlib.sha256(b).hexdigest()


def check():
    source = SOURCE.read_bytes()
    demand(sha(source) == SOURCE_SHA, 'frozen fully read source')
    tree = ast.parse(source)
    text = source.decode()
    calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call)]
    git_commands = sorted({n.args[0].value for n in calls if isinstance(n.func, ast.Name) and n.func.id == 'git' and n.args and isinstance(n.args[0], ast.Constant)})
    demand(git_commands == ['cat-file', 'hash-object', 'ls-files', 'show', 'update-index'], 'exact narrow Git operations')
    demand(not any(isinstance(n.func, ast.Attribute) and n.func.attr in ['unlink', 'rmdir', 'remove', 'rename', 'replace', 'write_bytes'] for n in calls), 'no deletion/move/source write')
    writes = [ast.unparse(n) for n in calls if isinstance(n.func, ast.Attribute) and n.func.attr == 'write_text']
    demand(len(writes) == 1 and writes[0].startswith('OUT.write_text('), 'only new publication receipt filesystem write')
    for literal in ["assert not OUT.exists()", "assert not (REPO / target).exists()", "assert not git('ls-files', '--stage', '--', target).strip()", "assert len(rows) == 57", "assert filtered == preexisting", "assert status.startswith('S ')", "assert git('show', ':' + row['git_tree_path']) == pathlib.Path(row['original_path']).read_bytes()", "assert git('cat-file', 'blob', blob) == data"]:
        demand(literal in text, 'reviewed preservation guard ' + literal)
    demand("'GIT_OBJECT_DIRECTORY': str(OBJECTS)" in text and "'GIT_INDEX_FILE': str(INDEX)" in text, 'separate root-owned pool/index')
    demand("git('update-index', '--skip-worktree', '--', *(row['git_tree_path'] for row in rows))" in text, 'skip-worktree scoped only to newly absent authenticated entries')
    demand("before['object_pool_bytes'] + payload + len(rows) * 4096 < 64 * 1024 * 1024" in text and "before['tmp_free_bytes'] > payload + len(rows) * 4096 + before['index_bytes'] + 2 * 1024 * 1024" in text, 'before writes object/index/payload/transient headroom')
    demand(text.count("> 8 * 1024 * 1024 + 131072") == 2 and "assert free('/workspace') > 8 * 1024 * 1024" in text, 'pre/post8MiB overlay reserve')
    result = P / 'lean/G6-NATURAL-COMMON-FACTORIZATION-MAIN-FCAD-FAILED-20261011T003950.153734Z-RESULT.json'
    raw = result.read_bytes()
    demand(sha(raw) == '1939fe2afec3c55f50406556c07a9181acb44881091897659bb1962803f6c83b' and (E / 'PRESERVATION-MANIFEST.json').read_bytes() == raw, 'unchanged result/fixed manifest bytes')
    m = json.loads(raw)
    demand(m['packet_distribution_complete'] is False and m['complete_lossless_export_original'] == str(E), 'historical fallback retained')
    expected = {r['path']: r for r in m['preserved_files']}
    actual = {str(x.relative_to(E)): x for x in E.rglob('*') if x.is_file()}
    demand(len(expected) == 55 and set(actual) == set(expected) | {'PRESERVATION-MANIFEST.json', 'COMPRESSED-DISTRIBUTIONS.json'}, 'exact57 saved input files')
    checks = []
    for rel, path in sorted(actual.items()):
        demand(not path.is_symlink(), 'no input symlink')
        b = path.read_bytes()
        if rel in expected:
            demand(len(b) == expected[rel]['bytes'] and sha(b) == expected[rel]['sha256'], 'saved file pin')
        elif rel == 'COMPRESSED-DISTRIBUTIONS.json':
            demand(sha(b) == m['compressed_distributions_manifest_sha256'], 'saved distribution pin')
        checks.append({'original_path': str(path), 'relative_path': rel, 'bytes': len(b), 'sha256': sha(b), 'expected_Git_SHA1_blob': hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()})
    prior = P / 'design/history/g6-natural-main-fcad-failure-saved-qc-20261011T0044Z-solver_design_recovery/FOURTH-LIVE-A080-PASS-FCAD-FAILURE-SAVED-QC-ATTEMPT1.json'
    demand(sha(prior.read_bytes()) == '34a434cc420b59e696964d5a95cedf7833abfaa82a8c4f8e3af64c6ff737c5bc', 'independent complete saved science/capture review')
    return {'status': 'PASS_SOURCE_ONLY_FIXED57_GIT_EVIDENCE_PUBLICATION_SCOPE', 'publisher_source': {'path': str(SOURCE), 'sha256': SOURCE_SHA, 'bytes': len(source)}, 'saved_input_pins': checks, 'exact_Git_commands': git_commands, 'prior_saved_review': {'path': str(prior), 'sha256': sha(prior.read_bytes())}, 'qualification': ['Root-owned publisher may index only this frozen57-file evidence export at genuinely absent new paths. It checks preexisting stage bytes unchanged, readbacks every Git blob/index entry, and sets skip-worktree only on those new paths.', 'This static gate does not execute Git, modify index flags or objects, establish a commit/remote push, or measure current execution resource availability. Actual publication must satisfy its dated before/post budget assertions and emit its own receipt.', 'Historical packet_distribution_complete=false and fixed-shmem capacity fallback remain unchanged. Git-only preservation is a separately qualified recoverable artifact, with local materialization absent.', 'No Lean/math/native producer, source edits, deletion, compiler/target rerun, or scientific acceptance is authorized by this gate. Prefix remains one strict kernel component; fcad/full141 fail.']}


def main():
    report = {'schema': 'fixed57_git_evidence_publisher_static_qc_v1', 'contributor': 'Codex / solver_design_recovery', 'observed_utc': datetime.now(timezone.utc).isoformat(), 'reviewer_sha256': sha(Path(__file__).read_bytes()), 'publisher_imported_or_executed': False, 'Git_commands_executed': 0}
    try:
        report.update(check())
    except Exception as e:
        report.update(status='FAIL_STATIC_QC', error_type=type(e).__name__, error=str(e))
    out = Path(sys.argv[1])
    with out.open('x') as f:
        json.dump(report, f, indent=2, sort_keys=True)
        f.write('\n')
    print(json.dumps({'status': report['status'], 'path': str(out), 'sha256': sha(out.read_bytes())}))
    return int(report['status'] == 'FAIL_STATIC_QC')


if __name__ == '__main__':
    raise SystemExit(main())
