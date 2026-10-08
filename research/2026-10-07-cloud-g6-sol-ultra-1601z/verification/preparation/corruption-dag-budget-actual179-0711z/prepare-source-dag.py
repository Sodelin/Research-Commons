"""Read-only future DAG exploration; never imports runner or invokes Lean."""
import ast
import hashlib
import json
import pathlib
import re
import sys

root = pathlib.Path('/workspace/cloud-lean')
reader = pathlib.Path('/workspace/g6-current-main')
author = pathlib.Path('/workspace/g6-auditor')
packet = 'research/2026-10-07-cloud-g6-sol-ultra-1601z'
plan = json.loads((root / packet / 'verification/freeze-plans/rational-zero-flag-actual178-repair-static.json').read_text())
pins = json.loads((root / packet / 'verification/preparation/corruption-closure-static-0600z/SOURCE-PINS.json').read_text())
runner_source = (root / packet / 'verification/run.py').read_text()
runner_ast = ast.parse(runner_source)
func = next(node for node in runner_ast.body if isinstance(node, ast.FunctionDef) and node.name == 'lean_imports')
namespace = {'re': re}
exec(compile(ast.Module(body=[func], type_ignores=[]), '<exact frozen lean_imports>', 'exec'), namespace)
lean_imports = namespace['lean_imports']
source_map = {name: {'path': str(pathlib.Path('/tmp/g6-frozen-62e937a2b58f00f6ed1197133650b6da2f96f71f') / record['repository_path']), 'repository_path': record['repository_path'], 'expected_sha256': record['sha256'], 'identity': 'actual179 frozen source'} for name, record in plan['modules'].items()}
# All179 providers are actualPASS at frozen62e, including Rationald9f.
for entry in pins['modules']:
    source_map[entry['module']] = {'path': str(root / entry['candidate_path']), 'repository_path': entry['original_path'], 'expected_sha256': entry['sha256'], 'identity': 'source-accepted original; staged exact copy'}
special = {
    'G6PairedTargetReuse': ('research/2026-10-08-cloud-paired-target-interface-repair-0429z/G6PairedTargetReuse.lean', '8c3d2e5cf636ec4efcb2846f75430cac1466a48c3d37f638ab36d1e3a32ace7b'),
    'G6NontrivialSplitFilter': ('research/2026-10-08-cloud-g6-nontrivial-split-filter-0319z/G6NontrivialSplitFilter.lean', '7d0faf7be18dacad7a606f91f895d06e0e5103dcde995321acba61e44dd4baf8'),
    'G6OriginalSpliceAdapter': ('research/2026-10-08-cloud-g6-original-g1-splice-reuse-0304z/G6OriginalSpliceAdapter.lean', '47af967837d2e2218f3513952f0d84d8919ca9a233d6f657cedc428393811d8e'),
    'BlobIncidentPorts': ('research/2026-10-08-cloud-nonplanar-blob-ports-0206z/BlobIncidentPorts.lean', 'e8b10a4e2d7e47629717f2d5db4459810731de249594ef69007f807b1510b4b8'),
    'HybridChildPorts': ('research/2026-10-08-cloud-nonplanar-child-ports-0202z/HybridChildPorts.lean', 'fb7a537de31543c7027fb64d173557cccebce19c768bdb0c432e627e84decdd9'),
}
for name, (path, sha) in special.items():
    source_map[name] = {'path': str(author / path), 'repository_path': path, 'expected_sha256': sha, 'identity': 'pinned original or explicitly reviewed derivative'}
g1directory = {pathlib.Path(entry['path']).stem: entry for entry in json.loads(pathlib.Path('/tmp/g6-corruption8-g1-source-directory.json').read_text()) if entry['name'].endswith('.lean')}
g1nested = {entry['path']: entry for entry in json.loads(pathlib.Path('/tmp/g6-corruption8-g1-nested-source-directory.json').read_text()) if entry['name'].endswith('.lean')}
g1root = 'research/2026-10-04-dot-complete-original-g1-1549z/src'
baseline = 'research/2026-10-04-dot-verified-lean-825-0203z/package/baseline'
search_roots = [reader / g1root, reader / baseline, *(reader / baseline / directory for directory in ['Imported', 'HistoricalCore', 'HistoricalNanuq', 'HistoricalBiological'])]
modules, missing, external, order = {}, [], set(), []

def visit(name):
    if name.startswith(('Mathlib.', 'Lean.', 'Std.', 'Init.')):
        external.add(name)
        return
    if name in modules:
        return
    record = source_map.get(name)
    if record is None:
        suffix = name.replace('.', '/') + '.lean'
        path = next((p / suffix for p in search_roots if (p / suffix).is_file()), None)
        if path is None:
            missing.append(name)
            return
        relative = str(path.relative_to(reader))
        record = {'path': str(path), 'repository_path': relative, 'identity': 'future original provider; not current179 acceptance'}
        if name in g1directory:
            record['expected_blob'] = g1directory[name]['sha']
            record['expected_bytes'] = g1directory[name]['size']
            record['remote_directory_identity'] = '73f7fda44fa43f293a9ab46774560f2b029f9758'
        elif relative in g1nested:
            record['expected_blob'] = g1nested[relative]['sha']
            record['expected_bytes'] = g1nested[relative]['size']
            record['remote_directory_identity'] = '73f7fda44fa43f293a9ab46774560f2b029f9758'
    path = pathlib.Path(record['path'])
    data = path.read_bytes()
    sha = hashlib.sha256(data).hexdigest()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    if 'expected_sha256' in record:
        assert sha == record['expected_sha256'], (name, sha, record['expected_sha256'])
    if 'expected_blob' in record:
        assert blob == record['expected_blob'], (name, blob, record['expected_blob'])
        assert len(data) == record['expected_bytes']
    deps = lean_imports(data.decode())
    modules[name] = {**record, 'sha256': sha, 'git_blob_sha': blob, 'bytes': len(data), 'imports': deps}
    for dep in deps:
        visit(dep)
    order.append(name)

scope = sys.argv[1] if len(sys.argv) > 1 else 'native'
new_targets = [entry['module'] for entry in pins['modules']]
if scope == 'generic':
    new_targets = [name for name in new_targets if name not in {'ActualSourceClosestCorruption', 'ActualSourceCorruptionClasses'}]
if scope == 'paired':
    new_targets = ['G6PairedTargetReuse']
targets = ([] if scope in {'native-only', 'paired'} else plan['targets']) + new_targets
for target in targets:
    visit(target)
new = sorted(set(modules) - set(plan['modules']))
result = {
    'status': 'LOCAL STATIC FUTURE DAG against actual179 PASS; no build/source freeze/dispatch',
    'baseline_frozen_input': '62e937a2b58f00f6ed1197133650b6da2f96f71f',
    'custom_modules': len(modules), 'extra_custom_modules': len(new), 'new_custom_modules': new,
    'modules': modules, 'targets': targets, 'topological_order': order,
    'external_roots': sorted(external), 'missing_custom': sorted(set(missing)),
    'remote_identity_gaps': sorted(name for name, record in modules.items() if record['identity'].startswith('future original') and 'remote_directory_identity' not in record),
    'accepted179_hashes_changed': False, 'compiler_invocations': 0,
    'scope': scope,
    'native_source_target_consumers_selected': scope != 'generic',
}
pathlib.Path('/tmp/g6-corruption-real-dag-actual179-' + scope + '-local.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({key: result[key] for key in ['custom_modules', 'extra_custom_modules', 'new_custom_modules', 'missing_custom', 'remote_identity_gaps']}, indent=2))
