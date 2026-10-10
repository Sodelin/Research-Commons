#!/usr/bin/env python3
"""Portable additive resource policy around the byte-pinned historical builder.

No old run, failed receipt, object, or author pathname is needed. A fresh source
run compiles components normally; exact-context cache reuse remains explicit.
The resource-qualified final is authoritative for this entrypoint's resource policy.
"""
from pathlib import Path
import argparse, datetime, hashlib, importlib.util, json, os, signal, sys, threading

ROOT = Path(__file__).resolve().parents[1]
CORE_SHA = 'f74f8e24dd6a61f627c42e4106de442f1ba0adecaf06442b6a0a4e70cbe681be'
AUDIT_SHA = 'f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a'
GRAPH_SHA = '44f673ff7c96b608e05ec7c7f01b469717c1d9089615403556d8ce9c20f51bf6'
THETA_SHA = 'e541af41b215cf473e63d4e968fdc42b31fe74f6384387f66de61f1ebbd7fbab'
EXCEPTIONS = {'connected/compatible': (1124, 300),
              'connected/20261009-canonical': (1411, 180)}
PLACEHOLDER = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def encoded_hash(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def verify_inputs(root=ROOT):
    require(__debug__, 'Python optimization disables historical assertions; do not use -O.')
    for path, expected in [('scripts/build_connected.py', CORE_SHA),
                           ('scripts/AuditTemplate.lean', AUDIT_SHA),
                           ('DEPENDENCY-GRAPH.json', GRAPH_SHA)]:
        require(digest(root / path) == expected, 'Pinned input differs: ' + path)
    graph = json.loads((root / 'DEPENDENCY-GRAPH.json').read_bytes())
    required = [k for k, v in graph['targets'].items()
                if v.get('required_for_accepted_release', True)]
    require(len(required) == len(set(required)) == 53, 'Required target set differs.')
    require(len(graph['targets']) == 78, 'Full profile inventory differs.')
    seen = set()
    for label, g in graph['targets'].items():
        require(len(g['order']) == len(set(g['order'])) == len(g['modules']),
                'Duplicate or incomplete selected order: ' + label)
        require(set(g['order']) == set(g['modules']) and set(g['roots']) <= set(g['order']),
                'Module/root coverage differs: ' + label)
        before = set()
        for module in g['order']:
            e = g['modules'][module]
            require(all(dep not in g['modules'] or dep in before for dep in e['imports']),
                    'Project imports are not topological: ' + module)
            before.add(module)
            if e['sha256'] not in seen:
                require(digest(root / 'source-store' / (e['sha256'] + '.lean')) == e['sha256'],
                        'Source-store content hash differs: ' + module)
                seen.add(e['sha256'])
    for label, (count, _) in EXCEPTIONS.items():
        g = graph['targets'][label]
        require(label in required and len(g['roots']) == len(g['order']) == count,
                'Aggregate exception scope differs: ' + label)
    return graph, required, len(seen)


def sources_for(g, template):
    require(template.count(PLACEHOLDER) == 1, 'Audit placeholder differs.')
    aggregate = '\n'.join('import ' + m for m in g['roots']) + '\n'
    audit = aggregate + template.replace(PLACEHOLDER, '#' + json.dumps(g['order'])).replace(
        '"AUDIT-OWNED.json"', '"AUDIT-RESULT.json"')
    return {k: hashlib.sha256(v.encode()).hexdigest()
            for k, v in [('aggregate', aggregate), ('complete-owned-audit', audit)]}


def invocation_policy(label, g, template, name, source_hash, obj, imports, seconds, memory, kind):
    """Validate the unchanged invocation and return its only permitted effective cap."""
    if kind == 'component':
        require(name in g['modules'], 'Component is outside the active profile.')
        e = g['modules'][name]
        theta = name == 'ThetaCertificate5' and e['sha256'] == THETA_SHA
        require(source_hash == e['sha256'] and obj is True and imports == e['imports'],
                'Component source/import contract differs.')
        require((seconds, memory) == ((600, 6144) if theta else (180, 4096)),
                'Component resource policy differs.')
        return memory
    require(kind in ['aggregate', 'complete-owned-audit'], 'Unrecognized invocation kind.')
    expected = sources_for(g, template)
    require(source_hash == expected[kind], 'Aggregate/audit source differs.')
    require(obj is (kind == 'aggregate'), 'Aggregate/audit object mode differs.')
    require(imports == g['roots'] + ([] if kind == 'aggregate' else ['Lean.Util.CollectAxioms']),
            'Aggregate/audit import coverage differs.')
    require(name == ('Connected_' + ''.join(c if c.isascii() and (c.isalnum() or c in '_-')
                                          else '_' for c in label)
                     if kind == 'aggregate' else 'OwnedAudit'), 'Generated target name differs.')
    expected_seconds = 300 if label == 'connected/compatible' else 180
    require(seconds == expected_seconds and memory == 4096, 'Original resource policy differs.')
    return 6144 if label in EXCEPTIONS else 4096


def first_namespace_file(roots, module):
    top = module.split('.')[0]
    root = next((p for p in roots if (p / top).is_dir() or (p / (top + '.olean')).is_file()), None)
    require(root is not None, 'No actual Lean namespace root: ' + module)
    path = root / (module.replace('.', '/') + '.olean')
    require(path.is_file(), 'Sparse namespace shadows an import: ' + module)
    return path


def memory_kib():
    vals = {line.split(':')[0]: int(line.split()[1])
            for line in Path('/proc/meminfo').read_text().splitlines()
            if line.startswith(('MemAvailable:', 'MemTotal:'))}
    require(len(vals) == 2 and 0 < vals['MemAvailable'] <= vals['MemTotal'],
            'Available memory cannot be measured reliably.')
    return vals


def guarded_call(builder, kind, call):
    initial = memory_kib()
    require(initial['MemAvailable'] >= 7168 * 1024,
            '6 GiB exception requires at least 7 GiB available before invocation.')
    stop, pressure = threading.Event(), threading.Event()
    samples, reasons = [], []

    def observe():
        while not stop.is_set():
            children = []
            try:
                current = memory_kib()
                row = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                       'memory_kib': current, 'children': []}
                for p in Path('/proc').iterdir():
                    if not p.name.isdigit():
                        continue
                    try:
                        fields = (p / 'stat').read_text().rsplit(')', 1)[1].split()
                        if int(fields[1]) != os.getpid() or (p / 'exe').resolve() != builder.bin / 'lean':
                            continue
                        children.append(int(p.name))
                        row['children'].append({'pid': int(p.name), **{
                            line.split(':')[0]: line.split(':', 1)[1].strip()
                            for line in (p / 'status').read_text().splitlines()
                            if line.startswith(('VmRSS:', 'VmHWM:'))}})
                    except (FileNotFoundError, ProcessLookupError):
                        continue
                samples.append(row)
                if current['MemAvailable'] < 1024 * 1024:
                    pressure.set(); reasons.append('Available memory below 1 GiB reserve.')
            except Exception as ex:
                pressure.set(); reasons.append('Memory/process observation uncertain: ' + repr(ex))
                try:
                    children = [int(x) for x in Path('/proc/self/task/' + str(os.getpid()) + '/children').read_text().split()]
                except Exception:
                    pass
            if pressure.is_set():
                for pid in children:
                    try:
                        os.kill(pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
            stop.wait(0.5)

    monitor = threading.Thread(target=observe, daemon=True)
    monitor.start()
    try:
        result = call()
    finally:
        stop.set(); monitor.join()
        builder._core.save(builder.run / ('MEMORY-' + builder._core.safe(builder.active_label)
                                        + '-' + kind + '-' + str(builder.attempt) + '.json'),
                           {'initial': initial, 'pressure_or_uncertainty': pressure.is_set(),
                            'reasons': reasons, 'samples': samples, 'sampling_seconds': 0.5,
                            'scope': 'Observed host available memory and direct Lean-child RSS/HWM; no unexposed cgroup-limit claim.'})
    require(not pressure.is_set(), 'Invocation stopped for memory pressure or uncertain observation.')
    return result


def make_builder(core):
    class ResourceQualifiedBuilder(core.Builder):
        def dependencies(self, context, modules):
            rows = super().dependencies(context, modules)
            for module, row in rows.items():
                require(Path(row['path']) == first_namespace_file([context] + self.external, module),
                        'Recorded import differs from actual namespace resolution: ' + module)
            return rows

        def target(self, label):
            self.active_label = label
            return super().target(label)

        def invoke(self, name, source, obj, imports, context, seconds, memory, kind):
            g = self.graph['targets'][self.active_label]
            require(context == self.run / 'targets' / core.safe(self.active_label) / 'objects',
                    'Invocation context is outside its active profile.')
            effective = invocation_policy(self.active_label, g, self.audit_template, name,
                                          digest(source), obj, imports, seconds, memory, kind)
            original = super().invoke
            call = lambda: original(name, source, obj, imports, context, seconds, effective, kind)
            result = guarded_call(self, kind, call) if effective == 6144 else call()
            rec, _ = result
            require(rec['cap_memory_mib'] == effective and rec['cap_seconds'] == seconds,
                    'Executed resource identity differs.')
            require(all(flag in rec['command'] for flag in ['-j1', '-t0', '-M' + str(effective),
                                                            '-Ddebug.skipKernelTC=false']),
                    'Executed kernel flags differ.')
            if kind == 'complete-owned-audit':
                # Preserve component failure-key handling in the unchanged core.
                # Its audit caller checks exit code; additionally require stable bindings here.
                require(rec['status'] == 'PASS_FRESH_KERNEL_CHECK' and rec['exit_code'] == 0
                        and rec['source_and_imports_stable'] and rec['native_initialized_libraries_bound'],
                        'Audit failed or its runtime/source/import binding is unstable.')
            return result
    ResourceQualifiedBuilder._core = core
    return ResourceQualifiedBuilder


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Validate pinned sources/configuration; run no compiler.')
    args = parser.parse_args()
    graph, required, source_count = verify_inputs()
    if args.check:
        print(json.dumps({'status': 'PASS_CONFIGURATION_AND_SOURCE_PINS_ONLY', 'required_targets': 53,
                          'all_inventory_targets': 78, 'distinct_source_versions': source_count,
                          'graph_sha256': GRAPH_SHA, 'core_sha256': CORE_SHA,
                          'fresh_compile_or_reproduction_claimed': False}))
        return 0
    spec = importlib.util.spec_from_file_location('pinned_connected_builder', ROOT / 'scripts/build_connected.py')
    core = importlib.util.module_from_spec(spec); spec.loader.exec_module(core)
    builder = make_builder(core)()
    require(builder.graph == graph and builder.graph_sha == GRAPH_SHA, 'Builder graph drift.')
    identity = {'portable_graph_sha256': GRAPH_SHA, 'core_builder_sha256': CORE_SHA,
                'audit_template_sha256': AUDIT_SHA, 'wrapper_sha256': digest(__file__),
                'compiler_sha256': core.BINARY, 'mathlib_commit': core.MATHLIB,
                'native_runtime_digest': builder.native_digest, 'required_targets': required,
                'ordinary_memory_mib': 4096, 'kernel_flags': ['-j1', '-t0', '-Ddebug.skipKernelTC=false'],
                'aggregate_and_complete_audit_exceptions': {
                    k: {'selected_module_count': n, 'memory_mib': 6144, 'wall_seconds_each': s,
                        'source_sha256': sources_for(graph['targets'][k], builder.audit_template)}
                    for k, (n, s) in EXCEPTIONS.items()},
                'existing_component_exception': {'module': 'ThetaCertificate5', 'source_sha256': THETA_SHA,
                                                 'memory_mib': 6144, 'wall_seconds': 600},
                'exception_headroom_mib': 7168, 'exception_safety_reserve_mib': 1024,
                'old_run_or_failure_receipt_required': False}
    identity['resource_identity_sha256'] = encoded_hash(identity)
    core.save(builder.run / 'RESOURCE-QUALIFIED-IDENTITY.json', identity)
    core.save(builder.run / 'CORE-FINAL-NEEDS-RESOURCE-QUALIFICATION.json', {
        'note': 'The unchanged core final describes the historical default policy. RESOURCE-QUALIFIED-FINAL.json and actual invocation receipts govern this additive entrypoint.'})
    (builder.run / 'RESOURCE-WRAPPER.py').write_bytes(Path(__file__).read_bytes())
    code = builder.run_targets(required)
    core_final = builder.run / 'FINAL-RECEIPT.json'
    complete = code == 0 and [r['target'] for r in builder.results] == required
    core.save(builder.run / 'RESOURCE-QUALIFIED-FINAL.json', {
        'status': 'PASS_ALL_53_RESOURCE_QUALIFIED_TARGETS' if complete else 'INCOMPLETE_PRESERVED_FAILURES',
        'resource_identity': identity, 'core_final_sha256': digest(core_final),
        'targets_passed': [r['target'] for r in builder.results if r['status'] == 'PASS'],
        'counts': dict(builder.counts), 'freshness': core.read(core_final)['fresh_every_selected_component_context_in_this_run'],
        'all_old_receipts_and_sources_preserved': True})
    return 0 if complete else 1


if __name__ == '__main__':
    raise SystemExit(main())
