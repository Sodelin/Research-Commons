#!/usr/bin/env python3
"""Independent byte, import and topological checks of public source contexts.

This is a static inventory check. It is not a Lean compilation receipt.
"""
import hashlib
import json
from pathlib import Path
import re

PACKET = Path(__file__).resolve().parents[1]


def clean_comments(source):
    # Preserve line breaks and support Lean's nested block comments. Imports
    # are top-level declarations, so quoted strings never contribute here.
    result, i, depth = [], 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            result.append('  ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            result.append('  ')
            i += 2
        elif depth:
            result.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            if end < 0:
                break
            result.append(' ' * (end - i))
            i = end
        else:
            result.append(source[i])
            i += 1
    if depth:
        raise ValueError('Unclosed Lean block comment')
    return ''.join(result)


def imports(source):
    cleaned = clean_comments(source)
    found = []
    for match in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)', cleaned, re.M):
        names = match[1].split()
        if not all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name) for name in names):
            raise ValueError('Unexpected import grammar: ' + match[1])
        found.extend(names)
    return found


def main():
    manifest = json.loads((PACKET / 'lean/SOURCE-MANIFEST.json').read_text())
    graph = json.loads((PACKET / 'lean/DEPENDENCY-GRAPH.json').read_text())
    failures, sources = [], {}
    for row in manifest['sources']:
        digest = row['sha256']
        path = PACKET / 'lean/source-store' / (digest + '.lean')
        raw = path.read_bytes()
        if digest in sources or len(raw) != row['bytes'] or hashlib.sha256(raw).hexdigest() != digest:
            failures.append('Source identity ' + digest)
        sources[digest] = imports(raw.decode('utf-8'))
    targets = []
    for name, context in graph['targets'].items():
        modules, order = context['modules'], context['order']
        before = {module: index for index, module in enumerate(order)}
        if len(before) != len(order) or set(before) != set(modules):
            failures.append(name + ': order is not exact module permutation')
        external = set()
        for module, row in modules.items():
            actual = sources[row['sha256']]
            if row['module'] != module or actual != row['imports']:
                failures.append(name + ': import identity ' + module)
            for provider in actual:
                if provider in modules:
                    if before.get(provider, len(order)) >= before.get(module, -1):
                        failures.append(name + ': provider order ' + provider + ' -> ' + module)
                else:
                    external.add(provider)
        if external != set(context['external_imports']):
            failures.append(name + ': external import closure')
        if not set(context['roots']) <= set(modules):
            failures.append(name + ': missing root')
        targets.append({'context': name, 'modules': len(modules),
                        'external_imports': len(external)})
    if manifest['source_count'] != len(sources) or manifest['target_count'] != len(targets):
        failures.append('Manifest census mismatch')
    if graph['held_1411_module_graph_included'] or graph['historical_53_certificate_replayed_or_reconstructed']:
        failures.append('Unpermitted claim about held/historical graph')
    result = {'status': 'STATIC_INVENTORY_PASS' if not failures else 'FAIL',
              'sources_checked': len(sources), 'contexts_checked': len(targets),
              'targets': targets, 'failures': failures,
              'source_replacements': graph['source_replacements'],
              'fresh_lean_compilation_verified': False,
              'master_mathematics_verified': False}
    path = PACKET / 'quality/SOURCE-GRAPH-REVIEW.json'
    path.write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({key: result[key] for key in ('status', 'sources_checked', 'contexts_checked', 'failures')}))
    return bool(failures)


if __name__ == '__main__':
    raise SystemExit(main())
