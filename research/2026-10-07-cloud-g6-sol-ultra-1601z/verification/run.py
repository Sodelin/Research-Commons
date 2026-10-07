"""Frozen-source serial verification; imported library cache is reuse, not rebuild."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys

root = pathlib.Path(sys.argv[1]).resolve()
targets = pathlib.Path(sys.argv[2]).read_text().split()
commit = sys.argv[3]
roots = [root, *(root / p for p in ['Imported', 'HistoricalCore', 'HistoricalNanuq', 'HistoricalBiological'])]
modules, external, order = {}, set(), []

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
    imports = []
    for line in data.decode().splitlines():
        match = re.match(r'\s*(?:public\s+)?import\s+(.+)', line)
        if match:
            imports.extend(match[1].split('--')[0].split())
    modules[name] = {'path': str(path.relative_to(root)), 'sha256': hashlib.sha256(data).hexdigest(), 'imports': imports}
    for dependency in imports:
        visit(dependency)
    order.append(name)

for target in targets:
    visit(target)
evidence = root / 'g6-evidence'
evidence.mkdir()
manifest = {'source_commit': commit, 'targets': targets, 'modules': modules,
            'topological_order': order, 'mathlib_roots': sorted(external)}
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

run(['lake', 'exe', 'cache', 'get', *sorted(external)], 'mathlib-cache')
for index, module in enumerate(order):
    record = modules[module]
    path = root / record['path']
    if hashlib.sha256(path.read_bytes()).hexdigest() != record['sha256']:
        raise RuntimeError('Frozen source mutated: ' + module)
    output = root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')
    output.parent.mkdir(parents=True, exist_ok=True)
    run(['lake', 'env', 'lean', '--trust=0', '-j1', '-M4096', '-o', str(output), str(path)], f'{index:03d}-{module}')
print('G6_SELECTED_COMPONENTS_PASSED commit=' + commit, flush=True)
