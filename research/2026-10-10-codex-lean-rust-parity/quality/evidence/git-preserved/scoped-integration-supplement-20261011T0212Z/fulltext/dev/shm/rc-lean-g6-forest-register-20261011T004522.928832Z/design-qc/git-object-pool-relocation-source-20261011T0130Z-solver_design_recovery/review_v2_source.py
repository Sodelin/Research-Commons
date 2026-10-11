"""Independent source/opaque-byte QC; does not import or invoke the relocation."""
import ast
import copy
import datetime
import hashlib
import json
import os
from pathlib import Path

WF = Path('/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z')
B = WF / 'metadata/git-evidence-publication'
Q = WF / 'design-qc/git-object-pool-relocation-source-20261011T0130Z-solver_design_recovery'
OLD = Path('/tmp/rc-cloud-git-objects-20261010T223739.438030Z')
PLAN = Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z/RESOURCE-AND-RUN-PLAN.json')

def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        while b := f.read(65536):
            h.update(b)
    return h.hexdigest()

def pin(p, expected):
    assert sha(p) == expected, str(p)
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': expected}

oldp = B / 'relocate_git_object_pool_losslessly_20261011.py'
newp = B / 'relocate_git_object_pool_losslessly_v2_20261011.py'
oldpin = pin(oldp, '7e92cda2d3b076f6edee1a597077202c04957ec90555eeb68538ec1b0a9caf50')
newpin = pin(newp, '53082e706eeb223b03f541d7af2b514f1a6be9c6aa4e1960ca930b2955a4d30f')
a, b = ast.parse(oldp.read_bytes()), ast.parse(newp.read_bytes())
actual = copy.deepcopy(b)
am = [n for n in a.body if isinstance(n, ast.FunctionDef) and n.name == 'main']
bm = [n for n in b.body if isinstance(n, ast.FunctionDef) and n.name == 'main']
assert len(am) == len(bm) == 1
tries = [n for n in bm[0].body if isinstance(n, ast.Try)]
assert len(tries) == 1
t = tries[0]
assert not t.orelse and not t.finalbody and len(t.handlers) == 1
assert ast.dump(t.handlers[0].type) == ast.dump(ast.Name(id='BaseException', ctx=ast.Load()))
rollback = ast.parse('''if OLD.is_symlink():
    OLD.unlink()
assert not OLD.exists() and BACKUP.is_dir()
BACKUP.rename(OLD)
assert inventory(OLD) == rows
raise
''').body
assert ast.dump(ast.Module(body=t.handlers[0].body, type_ignores=[])) == ast.dump(ast.Module(body=rollback, type_ignores=[]))
i = bm[0].body.index(t)
bm[0].body[i:i+1] = t.body
outer = b.body[-1]
assert isinstance(outer, ast.If) and len(outer.body) == 1 and isinstance(outer.body[0], ast.Try)
entry = outer.body[0]
assert ast.dump(ast.Module(body=entry.body, type_ignores=[])) == ast.dump(ast.Module(body=a.body[-1].body, type_ignores=[]))
assert not entry.orelse and not entry.finalbody and len(entry.handlers) == 1
assert ast.dump(entry.handlers[0].type) == ast.dump(ast.Name(id='BaseException', ctx=ast.Load()))
assert entry.handlers[0].name == 'error'
b.body[-1] = copy.deepcopy(a.body[-1])
assert ast.dump(a) == ast.dump(b), 'Unapproved source change outside rollback and failure trace'
constants = [n.value for n in ast.walk(actual) if isinstance(n, ast.Constant)]
for value in ('RELOCATION_FAILED_ALL_SURVIVING_POOLS_PRESERVED', 'pool_states', 'partial_counted_copy_deleted', 'source_cache_attempt_receipt_index_reference_changes'):
    assert value in constants
attrs = [n for n in ast.walk(actual) if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)]
assert sum(ast.unparse(n.func) == 'shutil.rmtree' for n in attrs) == 1
assert sum(ast.unparse(n.func) == 'OLD.unlink' for n in attrs) == 1
assert not any(ast.unparse(n.func).startswith(('subprocess.', 'os.system', 'os.exec')) for n in attrs)

priorp = Q / 'OBJECT-POOL-RELOCATION-V1-SOURCE-QC.json'
priorpin = pin(priorp, 'd1a45ca6222f09ad594a27d47891afb62ff2d7e2ab0174961ccbed10ee348aff')
prior = json.loads(priorp.read_bytes())
rows = prior['actual_input_inventory']['rows']
assert OLD.is_dir() and not OLD.is_symlink()
assert not (WF / 'metadata/git-object-pool-preserved-20261011').exists()
assert not Path('/tmp/rc-cloud-git-objects-verified-redirect-backup-20261011').exists()
paths = []
for p in sorted(OLD.rglob('*')):
    assert not p.is_symlink()
    if p.is_file():
        st = p.stat()
        paths.append({'path': str(p.relative_to(OLD)), 'bytes': st.st_size, 'allocated_bytes': st.st_blocks * 512, 'sha256': sha(p)})
    else:
        assert p.is_dir()
assert paths == rows and len(rows) == 2261
assert sum(r['bytes'] for r in rows) == 55754823
assert sum(r['allocated_bytes'] for r in rows) == 62386176
planpin = pin(PLAN, '0db1bb265fec8e2a4c89b0361d2b48f3f38c17d35aeb479b623c0954f097bac5')
plan = json.loads(PLAN.read_bytes())
roots = plan['allocation_roots']
assert len(roots) == len(set(roots)) == 25 and str(WF) in roots
assert plan['scratch_abort_bytes'] == 2013265920
assert plan['scratch_hard_limit_bytes'] == 2147483648
assert plan['memory_abort_bytes'] == 16106127360
assert not any((Path(r) / 'ACTIVE-GUARDED-PROCESS.json').exists() for r in roots)
seen, allocation = set(), 0
for root in roots:
    assert Path(root).is_dir()
    for directory, dirs, files in os.walk(root, followlinks=False):
        for p in [Path(directory), *(Path(directory) / n for n in files)]:
            st = p.lstat()
            k = st.st_dev, st.st_ino
            if k not in seen:
                seen.add(k)
                allocation += st.st_blocks * 512
mem = dict(line.split() for line in Path('/sys/fs/cgroup/memory.stat').read_text().splitlines())
nonreclaim = sum(int(mem[k]) for k in ('anon', 'shmem', 'kernel'))
reserve = 62386176 + (len(rows) + 512) * 4096
assert allocation + reserve + 79691776 < 2013265920
assert nonreclaim + reserve < 16106127360
report = {
    'schema': 'git_object_pool_lossless_relocation_source_design_qc_v2',
    'contributor': 'Codex / solver_design_recovery',
    'observed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'status': 'PASS_SOURCE_ONLY_NARROW_ROLLBACK_AND_FAILURE_TRACE',
    'source_v1': oldpin, 'source_v2': newpin, 'preserved_specific_v1_hold': priorpin,
    'whole_ast_check': 'Full source AST equals V1 after unwrapping only the redirect rollback try and replacing only the outer entrypoint failure trace.',
    'opaque_input_revalidation': {'files': len(rows), 'content_bytes': 55754823, 'allocated_bytes': 62386176, 'all_exact_prior_rows_rehashed': True},
    'dated_capacity': {'plan': planpin, 'allocation_roots': roots, 'markers_absent': True, 'scratch_bytes': allocation, 'nonreclaim_bytes': nonreclaim, 'copy_reserve_bytes': reserve, 'next_proof_reserve_bytes': 79691776, 'scratch_with_copy_and_next': allocation + reserve + 79691776},
    'data_preservation': [
        'Pre-redirect copy failures retain the original regular pool and any partial create-new counted copy.',
        'Caught redirect or logical/backup hash failures unlink only the new redirect, restore the verified original backup to the logical path, rehash it and re-raise.',
        'Only the redundant backup is removed after all original and counted object bytes have been verified. Failures after successful redirection retain the complete counted pool and logical redirect.',
        'The outer failure trace records surviving OLD/NEW/BACKUP states; a failure to write that create-new trace reports pool states to stdout.'
    ],
    'qualification': 'Source-only review, not invocation or completed relocation. This is ordinary caught-exception recovery, not atomic path availability across SIGKILL/power loss or a durability claim for shared memory. A rollback filesystem error still requires recovery from surviving pools. Recheck exact 25-root plan, idle markers and resource limits at invocation; a new producer context requires a new bound plan.',
    'git_commands_or_mutations': 0,
    'target_module_or_producer_imports_or_runs': 0,
    'prior_reader_writer_preflight': 'A prior reader-file writer failed Python parsing due nested string delimiters before writing or executing any reader. This immutable reader corrects only its own construction.'
}
out = Q / 'OBJECT-POOL-RELOCATION-V2-SOURCE-QC-ATTEMPT1.json'
with out.open('x') as f:
    json.dump(report, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps({'receipt': str(out), 'sha256': sha(out), 'status': report['status'], 'scratch_with_copy_and_next': report['dated_capacity']['scratch_with_copy_and_next']}))
