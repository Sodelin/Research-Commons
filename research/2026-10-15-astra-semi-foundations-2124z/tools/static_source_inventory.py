"""Read text/Git metadata only; never invokes Lean, Lake, an installer, or a model.
Usage: python -B static_source_inventory.py SOURCE_PACKAGE PINNED_MATHLIB
This lexical inventory is not a compiler dependency or object/runtime audit.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root, math = map(Path, sys.argv[1:])
pin = '0df444a360eaa60ab8c11dca51a86af692955474'

def git(base, *args):
    return subprocess.check_output(['git', '-C', str(base), *args], text=True)

assert git(math, 'rev-parse', 'HEAD').strip() == pin
locked = json.loads((math / 'lake-manifest.json').read_text())
repos = [('mathlib', math, pin, 'https://github.com/leanprover-community/mathlib4')]
for item in locked['packages']:
    base = math / '.lake/packages' / item['name']
    assert git(base, 'rev-parse', 'HEAD').strip() == item['rev']
    repos.append((item['name'], base, item['rev'], item['url']))

lookup = {}
for name, base, ref, _ in repos:
    for line in git(base, 'ls-tree', '-r', ref).splitlines():
        info, path = line.split('\t', 1)
        _, kind, blob = info.split()
        if kind == 'blob' and path.endswith('.lean'):
            module = path[:-5].replace('/', '.')
            lookup.setdefault(module, []).append((name, base, path, ref, blob))

def visible(text):
    """Elide nested comments and strings, retaining newlines; not a Lean parser."""
    out, i, depth, string = [], 0, 0, False
    while i < len(text):
        pair, char = text[i:i + 2], text[i]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2; continue
            if pair == '-/':
                depth -= 1; out.extend('  '); i += 2; continue
            out.append('\n' if char == '\n' else ' '); i += 1; continue
        if string:
            if char == '\\':
                out.extend('  '); i += 2; continue
            if char == '"':
                string = False
            out.append('\n' if char == '\n' else ' '); i += 1; continue
        if pair == '/-':
            depth = 1; out.extend('  '); i += 2; continue
        if pair == '--':
            end = text.find('\n', i)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - i)); i = end; continue
        if char == '"':
            string = True; out.append(' '); i += 1; continue
        out.append(char); i += 1
    return ''.join(out)

def imports(data):
    found = []
    for line in visible(data.decode('utf8')).splitlines():
        match = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)$', line)
        if match:
            found.extend(x for x in match[1].split()
                         if re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', x))
    return sorted(set(found))

owned = {p.relative_to(root / 'source').as_posix()[:-5].replace('/', '.'): p
         for p in (root / 'source').rglob('*.lean')}
selected, external, boundary, unknown, todo = {}, {}, set(), set(), list(owned)
while todo:
    module = todo.pop()
    if module in selected or module in external or module in boundary or module in unknown:
        continue
    if module in owned:
        path = owned[module]
        data = path.read_bytes()
        record = {'path': path.relative_to(root).as_posix(), 'bytes': len(data),
                  'sha256': hashlib.sha256(data).hexdigest(), 'imports': imports(data)}
        selected[module] = record
    elif module in lookup:
        candidates = lookup[module]
        if len(candidates) != 1:
            raise RuntimeError('ambiguous selected source module: ' + module)
        name, base, path, ref, blob = candidates[0]
        data = (base / path).read_bytes()
        actual = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        assert actual == blob, module
        record = {'repository': name, 'ref': ref, 'path': path, 'bytes': len(data),
                  'git_blob': blob, 'sha256': hashlib.sha256(data).hexdigest(), 'imports': imports(data)}
        external[module] = record
    elif module.split('.')[0] in {'Init', 'Lean', 'Std', 'Lake'}:
        boundary.add(module)
        continue
    else:
        unknown.add(module)
        continue
    todo.extend(record['imports'])
boundary.add('Init')  # Implicit standard prelude is an explicit core boundary.
assert not unknown, sorted(unknown)

ordered, visiting = [], set()
def visit(module):
    if module in ordered:
        return
    if module in visiting:
        raise RuntimeError('owned import cycle: ' + module)
    visiting.add(module)
    for dep in selected[module]['imports']:
        if dep in selected:
            visit(dep)
    visiting.remove(module)
    ordered.append(module)
for module in sorted(selected):
    visit(module)

manifest = {
    'schema': 'semi_static_source_closure_v1',
    'stage': 'STATIC_SOURCE_READ_ONLY_NOT_OBJECT_OR_RUNTIME_ADMISSION',
    'mathlib_ref': pin,
    'source_repositories': [{'name': n, 'ref': r, 'url': u} for n, _, r, u in repos],
    'owned_sources': dict(sorted(selected.items())), 'owned_topological_order': ordered,
    'external_sources': dict(sorted(external.items())),
    'unexpanded_toolchain_import_boundary': sorted(boundary),
    'unknown_source_modules': sorted(unknown),
    'external_source_count': len(external),
    'external_source_bytes': sum(x['bytes'] for x in external.values()),
    'source_authentication': 'Every selected external source Git-blob matched its held pinned repository tree. No object authentication or desktop availability is inferred.',
    'closure_limit': 'Lexical import graph and explicit core boundary; not a compiler/runtime/dynamic dependency inventory.',
    'compiler_invocations': 0, 'build_status': 'UNEXECUTED'}
output = root / 'STATIC-SOURCE-CLOSURE-01.json'
output.write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + '\n')
summary = {k: manifest[k] for k in ['external_source_count', 'external_source_bytes',
                                 'owned_topological_order', 'unknown_source_modules']}
summary.update({'manifest_bytes': output.stat().st_size,
                'manifest_sha256': hashlib.sha256(output.read_bytes()).hexdigest(),
                'toolchain_boundary_modules': len(boundary)})
(root / 'STATIC-SOURCE-CLOSURE-SUMMARY-01.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary))
