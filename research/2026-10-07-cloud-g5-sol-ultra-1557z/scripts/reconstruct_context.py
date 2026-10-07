#!/usr/bin/env python3
"""Freeze exact published G2 providers and their custom import closure.

Run from a pinned Commons checkout. No proof objects or shared files are edited.
Conflicting historical versions are recorded; explicit later canonical source
entries supersede earlier selections. Missing/ambiguous sources are fatal.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

p = argparse.ArgumentParser()
p.add_argument('repository', type=Path)
p.add_argument('destination', type=Path)
a = p.parse_args()
r, out = a.repository.resolve(), a.destination.resolve()
baseline = r / 'research/2026-10-04-dot-verified-lean-825-0203z/package/baseline'
selected, replacements = {}, []

def sha(f):
    return hashlib.sha256(f.read_bytes()).hexdigest()

def install(module, source, expected=None, authority='baseline', replace=True):
    source = source.resolve()
    actual = sha(source)
    if expected and actual != expected:
        raise ValueError(f'hash mismatch: {module} {source} {actual} != {expected}')
    if module in selected:
        if selected[module]['sha256'] == actual or not replace:
            return
        replacements.append({'module': module, 'old': selected[module],
                             'new_source': str(source.relative_to(r)), 'new_sha256': actual})
    selected[module] = {'source': str(source.relative_to(r)), 'sha256': actual,
                        'authority': authority}

for folder in ['Imported', 'HistoricalCore', 'HistoricalNanuq', 'HistoricalBiological', 'UnifiedLean']:
    for f in sorted((baseline / folder).rglob('*.lean')):
        name = '.'.join(f.relative_to(baseline if folder == 'UnifiedLean' else baseline / folder).with_suffix('').parts)
        install(name, f)

contexts = [
    '2026-10-07-dot-g2-accepted-source-preservation-0006z/SOURCE-AND-DEPENDENCY-PINS.json',
    '2026-10-07-dot-g2-calendar-tail-source-successor-0058z/SOURCE-AND-DEPENDENCY-PINS.json',
    '2026-10-07-dot-g2-chronological-decoration-integration-0139z/SOURCE-AND-DEPENDENCY-PINS.json',
    '2026-10-07-dot-g2-age-reader-source-preservation-0253z/SOURCE-AND-DEPENDENCY-PINS.json',
    '2026-10-07-dot-g2-matrix-and-ancestral-support-0418z/SOURCE-AND-REVIEW-PINS.json',
    '2026-10-07-dot-g2-actual-calendar-pair-support-0456z/PUBLIC-DEPENDENCIES.json',
    '2026-10-07-dot-g2-strict-clock-compatibility-0645z/PUBLIC-DEPENDENCIES.json',
    '2026-10-07-dot-g2-actual-age-support-certificate-0723z/PUBLIC-SOURCE-CONTEXT.json',
    '2026-10-07-dot-g2-calendar-first-age-binding-0745z/PUBLIC-SOURCE-CONTEXT.json',
    '2026-10-07-dot-g2-complete-timed-support-0858z/PUBLIC-SOURCE-CONTEXT.json',
    '2026-10-07-dot-g2-timed-endpoint-ordinary-integration-0941z/PUBLIC-SOURCE-CONTEXT.json',
]

def source_for(rec, directory, module, expected):
    s = rec.get('source', rec)
    for obj in [s, rec]:
        for key in ['public_path', 'path', 'file']:
            v = obj.get(key)
            if v:
                for f in [r / v, directory / v]:
                    if f.is_file() and (not expected or sha(f) == expected):
                        return f
        for key, v in obj.items():
            if 'url' in key and isinstance(v, str) and '/blob/' in v:
                rel = v.split('/blob/', 1)[1].split('/', 1)[1]
                f = r / rel
                if f.is_file() and (not expected or sha(f) == expected):
                    return f
    # A source entry can omit its local file when its basename is canonical.
    for f in [directory / (module + '.lean'), directory / 'sources' / (module + '.lean')]:
        if f.is_file() and (not expected or sha(f) == expected):
            return f
    return None

def visit(obj, directory, authority, canonical=False):
    if isinstance(obj, dict):
        module = obj.get('module')
        s = obj.get('source', obj)
        expected = s.get('sha256', s.get('source_sha256', obj.get('source_sha256')))
        if module and expected:
            f = source_for(obj, directory, module, expected)
            if f:
                install(module, f, expected, authority, replace=canonical)
        for key, value in obj.items():
            visit(value, directory, authority,
                  canonical=key in ['sources', 'selected_source', 'selected_sources', 'included_sources', 'records', 'chosen_additive_context'])
    elif isinstance(obj, list):
        for value in obj:
            visit(value, directory, authority, canonical)

for context in contexts:
    f = r / 'research' / context
    visit(json.loads(f.read_text()), f.parent, str(f.relative_to(r)))

for name, rel in [
    ('G5HiddenRegisterTimedProjectivity', 'research/2026-10-07-astra-g5-m3-7e3b/sources/G5HiddenRegisterTimedProjectivity.lean'),
    ('G5FrozenTriplePolynomialKernel', 'research/2026-10-07-codex-g5-lean/sources/G5FrozenTriplePolynomialKernel.lean'),
    ('G5FrozenTripleAnalyticSupport', 'research/2026-10-07-cloud-g5-sol-ultra-1557z/sources/G5FrozenTripleAnalyticSupport.lean'),
]:
    install(name, r / rel, authority='G5 assignment')

def imports(f):
    text, clean, depth, i = f.read_text(), [], 0, 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            i += 2
        elif depth:
            if text[i] == '\n':
                clean.append('\n')
            i += 1
        else:
            clean.append(text[i])
            i += 1
    return [m for line in ''.join(clean).splitlines() if line.startswith('import ')
            for m in line.split('--', 1)[0].removeprefix('import ').split()]

order, external, visiting = [], set(), set()
def walk(name):
    if name.startswith(('Mathlib.', 'Lean.', 'Init', 'Std.')):
        external.add(name)
        return
    if name in order:
        return
    if name in visiting:
        raise ValueError(f'cyclic import {name}')
    if name not in selected:
        raise ValueError(f'unresolved custom module {name}')
    visiting.add(name)
    rec = selected[name]
    rec['imports'] = imports(r / rec['source'])
    for dep in rec['imports']:
        walk(dep)
    visiting.remove(name)
    order.append(name)

walk('G5HiddenRegisterTimedProjectivity')
walk('G5FrozenTriplePolynomialKernel')
walk('G5FrozenTripleAnalyticSupport')
manifest = {'source_commit': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=r, text=True).strip(),
            'toolchain': 'leanprover/lean4:v4.33.1',
            'mathlib_commit': '0df444a360eaa60ab8c11dca51a86af692955474',
            'contexts': contexts, 'historical_replacements': replacements,
            'order': order, 'modules': {}, 'external_roots': sorted(external),
            'scope': 'Authenticated source selection only; compilation and complete audits are separate.'}
for name in order:
    rec = selected[name].copy()
    if name.startswith('G2'):
        dest = Path('TimedG2') / (name + '.lean')
    elif name in ['G5HiddenRegisterTimedProjectivity', 'G5FrozenTriplePolynomialKernel', 'G5FrozenTripleAnalyticSupport']:
        dest = Path('CloudG5') / (name + '.lean')
    else:
        src = Path(rec['source']).relative_to(baseline.relative_to(r))
        dest = src
    (out / dest).parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(r / rec['source'], out / dest)
    rec['destination'] = str(dest)
    manifest['modules'][name] = rec
(out / 'SOURCE-CONTEXT.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(json.dumps({'custom_modules': len(order), 'external_roots': len(external),
                  'historical_replacements': len(replacements), 'manifest': str(out / 'SOURCE-CONTEXT.json')}))
