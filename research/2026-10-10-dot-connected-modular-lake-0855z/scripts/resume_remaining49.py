#!/usr/bin/env python3
"""Scheduling-only continuation of the exact frozen 53-target graph.

Four terminal target passes are reauthenticated; the unchanged reviewed Builder
executes the other 49. A union receipt is written only after their terminal result.
This never inserts old passes into a new run's native FINAL-RECEIPT.
"""
from pathlib import Path
import argparse, hashlib, json, os, subprocess
import build_connected as bc

ROOT = bc.ROOT
GRAPH = '7e4b02f6b482a2e237432ba629f6a09211e72eae483310abe9d72baad46be061'
RUNNER = 'f74f8e24dd6a61f627c42e4106de442f1ba0adecaf06442b6a0a4e70cbe681be'
PRIOR = ROOT / '.build/runs/20261010T011059.081834Z'
REUSED = ['825/base', '825/main', '825/pure-induction-v2', '825/graph-repair']
HASHES = {}

def digest(path):
    path = Path(path)
    s = path.stat()
    key = (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
    if key not in HASHES:
        HASHES[key] = hashlib.sha256(path.read_bytes()).hexdigest()
        t = path.stat()
        assert key == (t.st_dev, t.st_ino, t.st_size, t.st_mtime_ns, t.st_ctime_ns)
    return HASHES[key]

def bundle(path):
    return {s: digest(bc.companion(path, s)) for s in bc.SUFFIXES
            if bc.companion(path, s).is_file()}

def verify(output):
    assert digest(ROOT / 'DEPENDENCY-GRAPH.json') == GRAPH
    assert digest(ROOT / 'scripts/build_connected.py') == RUNNER
    graph = bc.read(ROOT / 'DEPENDENCY-GRAPH.json')
    required = [k for k, v in graph['targets'].items()
                if v.get('required_for_accepted_release', True)]
    remaining = [k for k in required if k not in REUSED]
    assert len(required) == 53 and len(remaining) == 49
    assert set(REUSED).isdisjoint(remaining) and set(REUSED + remaining) == set(required)
    assert {'connected/compatible', 'connected/20261009-canonical'} <= set(remaining)
    pins = bc.read(PRIOR / 'RUNNER-AND-INPUT-PINS.json')
    assert pins['graph_sha256'] == GRAPH and pins['builder_sha256'] == RUNNER
    assert digest(PRIOR / 'DEPENDENCY-GRAPH.json') == GRAPH
    template = (ROOT / 'scripts/AuditTemplate.lean').read_text()
    assert pins['audit_template_sha256'] == digest(ROOT / 'scripts/AuditTemplate.lean')
    leanbin = Path(os.environ['CONNECTED_LEAN_BIN']).resolve()
    mathlib = Path(os.environ['CONNECTED_MATHLIB']).resolve()
    assert digest(leanbin / 'lean') == bc.BINARY
    assert subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip() == bc.MATHLIB
    external = sorted((mathlib / '.lake/packages').glob('*/.lake/build/lib/lean')) + [mathlib / '.lake/build/lib/lean', leanbin.parent / 'lib/lean']
    native = bc.read(PRIOR / 'NATIVE-RUNTIME-PINS.json')
    assert all(digest(p) == v['sha256'] for p, v in native['libraries'].items())

    def imports(context, names):
        answer = {}
        for name in names:
            rel = name.replace('.', '/') + '.olean'
            path = next((r / rel for r in [context] + external if (r / rel).is_file()), None)
            assert path is not None, ('Missing exact import', name)
            answer[name] = bundle(path)
        return answer

    def receipt(r, context, names, source_hash):
        assert r['status'] == 'PASS_FRESH_KERNEL_CHECK' and r['exit_code'] == 0
        assert r['source_sha256'] == source_hash and r['compiler_sha256'] == bc.BINARY and r['mathlib_commit'] == bc.MATHLIB
        theta = r['module'] == 'ThetaCertificate5' and source_hash == 'e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab'
        memory = 6144 if theta else 4096
        assert r['cap_memory_mib'] == memory
        if theta:
            assert r['cap_seconds'] == 600
        assert all(x in r['command'] for x in ['-j1', '-t0', '-M' + str(memory), '-Ddebug.skipKernelTC=false'])
        assert r['source_and_imports_stable'] and r['native_runtime_stat_stable'] and r['native_initialized_libraries_bound']
        assert r['native_runtime_digest'] == native['native_runtime_digest']
        actual = imports(context, names)
        assert r['direct_import_artifacts'] == actual
        assert r['direct_import_sha256'] == {m: a['.olean'] for m, a in actual.items()}
        rd = Path(r['receipt_directory'])
        original = bc.read(rd / 'receipt.json')
        assert all(r[k] == v for k, v in original.items())
        assert digest(rd / 'stdout') == r['stdout_sha256'] and digest(rd / 'stderr') == r['stderr_sha256']
        assert 'sorryAx' not in (rd / 'stdout').read_text(errors='replace') + (rd / 'stderr').read_text(errors='replace')
        for v in r['native_loader_outputs']:
            assert digest(v['path']) == v['sha256']
        for p, v in r['native_initialized_libraries'].items():
            assert digest(p) == v['sha256']
        frozen = Path(r['working_directory']) / (r['module'].replace('.', '/') + '.lean')
        assert digest(frozen) == source_hash

    verified = []
    for label in REUSED:
        g = graph['targets'][label]
        target = PRIOR / 'targets' / bc.safe(label)
        context = target / 'objects'
        result_path = target / 'RESULT.json'
        r = bc.read(result_path)
        assert r['status'] == 'PASS' and r['target'] == label
        assert r['roots'] == len(g['roots']) and r['closure_modules'] == len(g['order'])
        assert [c['module'] for c in r['component_receipts']] == g['order']
        for c in r['component_receipts']:
            e = g['modules'][c['module']]
            assert digest(ROOT / 'source-store' / (e['sha256'] + '.lean')) == e['sha256']
            receipt(c, context, e['imports'], e['sha256'])
            assert bundle(context / (c['module'].replace('.', '/') + '.olean')) == c['object_artifacts']
        aggregate = '\n'.join('import ' + m for m in g['roots']) + '\n'
        receipt(r['aggregate_receipt'], context, g['roots'], hashlib.sha256(aggregate.encode()).hexdigest())
        name = r['aggregate_receipt']['module']
        assert bundle(context / (name + '.olean')) == r['aggregate_receipt']['object_artifacts']
        audit_body = template.replace('#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]', '#' + json.dumps(g['order'])).replace('"AUDIT-OWNED.json"', '"AUDIT-RESULT.json"')
        audit_source = aggregate + audit_body
        ar = r['audit_receipt']
        receipt(ar, context, g['roots'] + ['Lean.Util.CollectAxioms'], hashlib.sha256(audit_source.encode()).hexdigest())
        audit_path = Path(ar['audit_output'])
        aux = next(x for x in ar['auxiliary_outputs'] if x['path'] == 'work/AUDIT-RESULT.json')
        assert digest(audit_path) == aux['sha256']
        audit = bc.read(audit_path)
        assert audit['selected_modules'] == g['order']
        assert not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']
        assert (r['declarations'], r['theorems']) == (audit['declaration_count'], audit['theorem_declaration_count'])
        inventory_path = target / 'ACTUAL-IMPORTED-ARTIFACTS.json'
        for a in bc.read(inventory_path):
            assert digest(a['path']) == a['sha256'] and Path(a['path']).stat().st_size == a['bytes']
        verified.append({'target': label, 'result_path': str(result_path), 'result_sha256': digest(result_path), 'audit_sha256': digest(audit_path), 'import_inventory_sha256': digest(inventory_path), 'component_count': len(g['order'])})
    report = {'status': 'PASS_EXACT_FOUR_PRIOR_TARGET_REAUTHENTICATION', 'graph_sha256': GRAPH, 'builder_sha256': RUNNER, 'wrapper_sha256': digest(Path(__file__)), 'prior_targets': verified, 'remaining_targets': remaining, 'required_targets': required, 'partition': '4 prior + 49 remaining = exact 53; disjoint and exhaustive', 'native_runtime_digest': native['native_runtime_digest'], 'union_of_runs': True, 'single_fresh_invocation_claimed': False}
    bc.save(output, report)
    return report

if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--verify-only', type=Path)
    args = ap.parse_args()
    if args.verify_only:
        verify(args.verify_only)
        print('PASS_EXACT_FOUR_PRIOR_TARGET_REAUTHENTICATION', flush=True)
    else:
        b = bc.Builder()
        report = verify(b.run / 'PRIOR-FOUR-REAUTHENTICATION.json')
        assert b.graph_sha == GRAPH and b.native_digest == report['native_runtime_digest']
        code = b.run_targets(report['remaining_targets'])
        bc.save(b.run / 'UNION-OF-RUNS-53.json', {**report, 'status': 'PASS_UNION_ALL_53_REQUIRED' if code == 0 else 'INCOMPLETE_UNION_FAILURES_PRESERVED', 'current_run': str(b.run), 'current_final_receipt_sha256': digest(b.run / 'FINAL-RECEIPT.json')})
        raise SystemExit(code)
