"""Frozen-source serial verification; imported library cache is reuse, not rebuild."""
import datetime
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
import complete_environment

root = pathlib.Path(sys.argv[1]).resolve()
targets = pathlib.Path(sys.argv[2]).read_text().split()
commit = sys.argv[3]
roots = [root, *(root / p for p in ['Imported', 'HistoricalCore', 'HistoricalNanuq', 'HistoricalBiological'])]
modules, external, order = {}, set(), []

def lean_imports(source):
    # Derivative of the hash-pinned G5 source selector. Lean block comments
    # nest; a prose line beginning with 'import' is not a dependency.
    clean, depth, index = [], 0, 0
    while index < len(source):
        if source[index:index + 2] == '/-':
            depth += 1
            index += 2
        elif depth and source[index:index + 2] == '-/':
            depth -= 1
            index += 2
        elif depth:
            if source[index] == '\n':
                clean.append('\n')
            index += 1
        else:
            clean.append(source[index])
            index += 1
    dependencies = []
    for line in ''.join(clean).splitlines():
        match = re.match(r'\s*(?:public\s+)?import\s+(.+)', line)
        if match:
            dependencies.extend(match[1].split('--')[0].split())
    return dependencies

def visit(name):
    if name.startswith('Mathlib.'):
        external.add(name)
        return
    if name.startswith(('Lean.', 'Std.', 'Init.')) or name in modules:
        return
    path = next((p / (name.replace('.', '/') + '.lean') for p in roots
                 if (p / (name.replace('.', '/') + '.lean')).is_file()), None)
    if path is None:
        raise RuntimeError('Missing custom source: ' + name)
    data = path.read_bytes()
    imports = lean_imports(data.decode())
    modules[name] = {'path': str(path.relative_to(root)), 'sha256': hashlib.sha256(data).hexdigest(), 'imports': imports}
    for dependency in imports:
        visit(dependency)
    order.append(name)

for target in targets:
    visit(target)
evidence = root / 'g6-evidence'
evidence.mkdir(exist_ok=True)
lean_executable = pathlib.Path(shutil.which('lean')).resolve()
dependencies = {
    'lean_version': subprocess.check_output(['lean', '--version'], text=True).strip(),
    'lean_executable_sha256': hashlib.sha256(lean_executable.read_bytes()).hexdigest(),
    'mathlib_commit': subprocess.check_output(
        ['git', '-C', str(root / 'deps/mathlib'), 'rev-parse', 'HEAD'], text=True).strip(),
    'lake_manifest_sha256': hashlib.sha256((root / 'lake-manifest.json').read_bytes()).hexdigest(),
    'lake_registration_sha256': hashlib.sha256((root / 'lakefile.lean').read_bytes()).hexdigest(),
    'verification_script_sha256': hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
    'complete_inventory_helper_sha256': hashlib.sha256(
        pathlib.Path(complete_environment.__file__).read_bytes()).hexdigest(),
    'complete_inventory_template_sha256': hashlib.sha256((
        pathlib.Path(__file__).resolve().parents[3] /
        'research/2026-10-05-dot-connected-modular-lean-workspace-2252z/'
        'package/scripts/AuditTemplate.lean').read_bytes()).hexdigest(),
}
if dependencies['mathlib_commit'] != '0df444a360eaa60ab8c11dca51a86af692955474':
    raise RuntimeError('Unexpected Mathlib commit')
if dependencies['lean_executable_sha256'] != 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550':
    raise RuntimeError('Unexpected Lean executable')
(evidence / 'lake-manifest.json').write_bytes((root / 'lake-manifest.json').read_bytes())
manifest = {'source_commit': commit, 'targets': targets, 'modules': modules,
            'topological_order': order, 'mathlib_roots': sorted(external),
            'dependencies': dependencies}
(evidence / 'inputs.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('G6_INPUTS ' + json.dumps(manifest), flush=True)

def run(argv, label):
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    print('G6_COMMAND ' + json.dumps({'argv': argv, 'cwd': str(root), 'start': start}), flush=True)
    try:
        result = subprocess.run(argv, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        output, code = result.stdout, result.returncode
    except subprocess.TimeoutExpired as exc:
        output, code = exc.stdout or b'', 124
    (evidence / (label + '.log')).write_bytes(output)
    print(output.decode(errors='replace'), end='', flush=True)
    receipt = {'argv': argv, 'start': start,
               'end': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'exit': code,
               'output_sha256': hashlib.sha256(output).hexdigest()}
    print('G6_RECEIPT ' + json.dumps(receipt), flush=True)
    (evidence / (label + '.json')).write_text(json.dumps(receipt, indent=2) + '\n')
    if code:
        raise SystemExit(code)
    if re.search(rb'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler', output):
        raise SystemExit('Forbidden proof axiom in report')
    return output.decode(errors='replace')

run(['lake', 'exe', 'cache', 'get', *sorted(external)], 'mathlib-cache')
passed_modules, failed_modules, blocked_modules = set(), [], []
for index, module in enumerate(order):
    record = modules[module]
    custom_dependencies = [dependency for dependency in record['imports'] if dependency in modules]
    if any(dependency not in passed_modules for dependency in custom_dependencies):
        blocked_modules.append({'module': module, 'dependencies': custom_dependencies})
        continue
    path = root / record['path']
    if hashlib.sha256(path.read_bytes()).hexdigest() != record['sha256']:
        raise RuntimeError('Frozen source mutated: ' + module)
    output = root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    try:
        run(['lake', 'env', 'lean', '--trust=0', '-j1', '-M4096', '-o', str(output), str(path)], f'{index:03d}-{module}')
    except SystemExit as exc:
        failed_modules.append({'module': module, 'result': str(exc.code)})
        continue
    passed_modules.add(module)

audited_targets = [target for target in targets if target in passed_modules]
(evidence / 'selected-results.json').write_text(json.dumps({
    'requested_targets': targets, 'passed_modules': sorted(passed_modules),
    'failed_modules': failed_modules, 'blocked_modules': blocked_modules,
    'audited_targets': audited_targets,
}, indent=2) + '\n')

# Audit every declaration in each selected G6 source. Each #print axioms report
# includes the complete transitive proof dependency set, including providers.
declarations, declarations_by_module = [], {}
for module in audited_targets:
    source = (root / modules[module]['path']).read_text()
    namespace = re.search(r'^namespace\s+(\S+)\s*$', source, re.MULTILINE)
    if namespace is None:
        raise RuntimeError('Selected source has no explicit namespace: ' + module)
    declarations_by_module[module] = [namespace[1] + '.' + name for name in re.findall(
        r'^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_\']+)',
        source, re.MULTILINE)]
    declarations.extend(declarations_by_module[module])
audit = evidence / 'DeclarationAudit.lean'
audit.write_text('\n'.join('import ' + module for module in audited_targets) + '\n\n' +
                 '\n'.join('#print axioms ' + name for name in declarations) + '\n')
audit_output = run(['lake', 'env', 'lean', '--trust=0', '-j1', '-M4096', str(audit)], 'declaration-audit')
reports = {name: [axiom.strip() for axiom in axioms.split(',') if axiom.strip()]
           for name, axioms in re.findall(
               r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit_output, re.DOTALL)}
reports.update({name: [] for name in re.findall(
    r"'([^']+)' does not depend on any axioms", audit_output)})
missing = sorted(set(declarations) - reports.keys())
unexpected = {name: sorted(set(axioms) - {'propext', 'Classical.choice', 'Quot.sound'})
              for name, axioms in reports.items()
              if set(axioms) - {'propext', 'Classical.choice', 'Quot.sound'}}
(evidence / 'axiom-audit.json').write_text(json.dumps({
    'declarations': declarations, 'transitive_axioms': reports,
    'declarations_by_module': declarations_by_module,
    'missing_reports': missing, 'unexpected_axioms': unexpected,
    'audit_source_sha256': hashlib.sha256(audit.read_bytes()).hexdigest(),
}, indent=2) + '\n')
if missing or unexpected:
    raise SystemExit('Incomplete or unexpected declaration axiom audit')
# Required full ownership/type/body/reference inventory, distinct from the
# named selected-source reports above. Only actual successful custom modules
# enter it, including generated declarations and inherited custom providers.
owned_modules = [module for module in order if module in passed_modules]
complete_audit = complete_environment.prepare(root, evidence,
    pathlib.Path(__file__).resolve().parents[3], owned_modules)
run(['lake', 'env', 'lean', '--trust=0', '-j1', '-M4096', str(complete_audit)],
    'complete-custom-environment-audit')
complete_environment.recover(root, evidence, owned_modules)
counts = {module: len(names) for module, names in declarations_by_module.items()}
print('CLOUD_SELECTED_AXIOM_AUDIT_PASSED ' + json.dumps(counts), flush=True)
g6_targets = [target for target in targets if target.startswith('UnifiedLean.G6.')]
if g6_targets and all(target in audited_targets for target in g6_targets):
    print('G6_AXIOM_AUDIT_PASSED declarations=' + str(sum(counts[target] for target in g6_targets)), flush=True)
    print('G6_SELECTED_COMPONENTS_PASSED commit=' + commit, flush=True)
for target in audited_targets:
    print('CLOUD_TARGET_PASSED ' + target + ' commit=' + commit, flush=True)
if failed_modules:
    raise SystemExit('Selected source failure: ' + json.dumps(failed_modules))
