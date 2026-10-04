#!/usr/bin/env python3
"""Pinned, resumable compiler builds of explicit non-colliding source profiles.

Borrowing a provider requires its actual matching fresh receipt. Every skipped
own attempt is rechecked against source, object, and direct import hashes.
No network download, source rewriting, axioms, admissions, or implicit flattening.
"""
from pathlib import Path
import argparse, collections, datetime, fcntl, hashlib, json, os, re, shutil, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / '.build'
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
COMPILER = '819816b2e0a3bf405af45ae5c7af2491d8f5bee6'
MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
PROFILE_ORDERS = {'base': ['base'], 'graph-repair': ['graph-repair', 'base'], 'theta': ['theta', 'graph-repair', 'base'], 'fair-g5-v1': ['fair-g5-v1', 'base'], 'fair-g5-normalization-v1': ['fair-g5-normalization-v1', 'fair-g5-v1', 'base'], 'fair-g5-sharpness-v1': ['fair-g5-sharpness-v1', 'fair-g5-normalization-v1', 'fair-g5-v1', 'base'], 'g1-contextual-v1': ['g1-contextual-v1', 'base'], 'g1-graph-v1': ['g1-graph-v1', 'g1-contextual-v1', 'base'], 'g1-joint-v1': ['g1-joint-v1', 'g1-contextual-v1', 'base'], 'g1-normalization-v1': ['g1-normalization-v1', 'g1-graph-v1', 'g1-joint-v1', 'g1-contextual-v1', 'base'], 'g1-temporal-v1': ['g1-temporal-v1', 'g1-joint-v1', 'g1-contextual-v1', 'base'], 'g1-interface-v1': ['g1-interface-v1', 'g1-normalization-v1', 'g1-graph-v1', 'g1-joint-v1', 'g1-contextual-v1', 'base'], 'g1-calendar-v1': ['g1-calendar-v1', 'g1-interface-v1', 'g1-normalization-v1', 'g1-graph-v1', 'g1-joint-v1', 'g1-contextual-v1', 'base'], 'g1-unranked-k-v1': ['g1-unranked-k-v1', 'g1-joint-v1', 'g1-contextual-v1', 'base'], 'main': ['main', 'g1-compact-v1', 'g1-completion-v1', 'g1-unranked-k-v1', 'g1-calendar-v1', 'g1-interface-v1', 'g1-temporal-v1', 'g1-normalization-v1', 'g1-joint-v1', 'g1-graph-v1', 'g1-contextual-v1', 'fair-g5-sharpness-v1', 'fair-g5-normalization-v1', 'fair-g5-v1', 'theta', 'graph-repair', 'base'], 'pure-induction-v2': ['pure-induction-v2', 'main', 'g1-compact-v1', 'g1-completion-v1', 'g1-unranked-k-v1', 'g1-calendar-v1', 'g1-interface-v1', 'g1-temporal-v1', 'g1-normalization-v1', 'g1-joint-v1', 'g1-graph-v1', 'g1-contextual-v1', 'fair-g5-sharpness-v1', 'fair-g5-normalization-v1', 'fair-g5-v1', 'theta', 'graph-repair', 'base'], 'g1-completion-v1': ['g1-completion-v1', 'g1-unranked-k-v1', 'g1-calendar-v1', 'g1-interface-v1', 'g1-normalization-v1', 'g1-temporal-v1', 'g1-joint-v1', 'g1-graph-v1', 'g1-contextual-v1', 'base'], 'g1-compact-v1': ['g1-compact-v1', 'g1-completion-v1', 'g1-unranked-k-v1', 'g1-calendar-v1', 'g1-interface-v1', 'g1-normalization-v1', 'g1-temporal-v1', 'g1-joint-v1', 'g1-graph-v1', 'g1-contextual-v1', 'base']}
AGGREGATE_NAMES = {'base': 'VerifiedBaseline', 'fair-g5-v1': 'VerifiedFairG5V1Profile', 'fair-g5-normalization-v1': 'VerifiedFairG5NormalizationV1Profile', 'fair-g5-sharpness-v1': 'VerifiedFairG5SharpnessV1Profile', 'g1-contextual-v1': 'VerifiedG1ContextualV1Profile', 'g1-graph-v1': 'VerifiedG1GraphV1Profile', 'g1-joint-v1': 'VerifiedG1JointV1Profile', 'g1-normalization-v1': 'VerifiedG1NormalizationV1Profile', 'g1-temporal-v1': 'VerifiedG1TemporalV1Profile', 'g1-interface-v1': 'VerifiedG1InterfaceV1Profile', 'g1-calendar-v1': 'VerifiedG1CalendarV1Profile', 'g1-unranked-k-v1': 'VerifiedG1UnrankedKV1Profile', 'main': 'VerifiedMainProfile', 'pure-induction-v2': 'VerifiedPureInductionProfile', 'g1-completion-v1': 'VerifiedG1CompletionProfile', 'g1-compact-v1': 'VerifiedG1CanonicalCompactProfile'}
STAGES = ['base', 'graph-repair', 'theta', 'fair-g5-v1', 'fair-g5-normalization-v1', 'fair-g5-sharpness-v1', 'g1-contextual-v1', 'g1-graph-v1', 'g1-joint-v1', 'g1-normalization-v1', 'g1-temporal-v1', 'g1-interface-v1', 'g1-calendar-v1', 'g1-unranked-k-v1', 'g1-completion-v1', 'g1-compact-v1', 'main', 'pure-induction-v2']
AUDITED_PROFILES = ['base', 'fair-g5-v1', 'fair-g5-normalization-v1', 'fair-g5-sharpness-v1', 'g1-contextual-v1', 'g1-graph-v1', 'g1-joint-v1', 'g1-normalization-v1', 'g1-temporal-v1', 'g1-interface-v1', 'g1-calendar-v1', 'g1-unranked-k-v1', 'g1-completion-v1', 'g1-compact-v1', 'main', 'pure-induction-v2']

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def read(path):
    return json.loads(path.read_bytes())

def save(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + '.tmp')
    tmp.write_text(json.dumps(data, indent=2) + '\n')
    tmp.replace(path)

def imports(path):
    text = path.read_bytes().decode('utf-8')
    # Source imports in this preserved corpus are standard top-level imports.
    return [m for line in text.splitlines() if line.startswith('import ')
            for m in line[7:].split() if not m.startswith('--')]

class Builder:
    def __init__(self):
        configured = os.environ.get('UNIFIED_LEAN_BIN') or os.environ.get('THETA_LEAN_BIN')
        if configured:
            self.bin = Path(configured).resolve()
        else:
            executable = shutil.which('lean')
            if not executable:
                raise RuntimeError('Source the documented shared pinned env.sh or set UNIFIED_LEAN_BIN')
            self.bin = Path(executable).resolve().parent
        version = subprocess.check_output([str(self.bin / 'lean'), '--version'], text=True)
        assert '4.33.1' in version and COMPILER in version, version
        self.compiler_binary_sha256 = digest(self.bin / 'lean')
        cache = os.environ.get('UNIFIED_MATHLIB_CACHE')
        if not cache:
            roots = os.environ.get('THETA_OBJECT_ROOTS', '').split(':')
            candidate = next((Path(x) for x in roots if '/mathlib/.lake/build/lib/lean' in x), None)
            if candidate is not None:
                cache = str(candidate.parents[3])
        if not cache:
            raise RuntimeError('Set UNIFIED_MATHLIB_CACHE to the existing pinned built mathlib checkout')
        self.mathlib = Path(cache).resolve()
        rev = subprocess.check_output(['git', '-C', str(self.mathlib), 'rev-parse', 'HEAD'], text=True).strip()
        assert rev == MATHLIB, ('mathlib pin differs', rev)
        self.external = [self.mathlib / '.lake/build/lib/lean']
        self.external += sorted((self.mathlib / '.lake/packages').glob('*/.lake/build/lib/lean'))
        self.registry = read(ROOT / 'catalog/SOURCE-REGISTRY.json')['records']
        self.byprofile = {}
        for row in self.registry:
            assert digest(ROOT / row['source']) == row['source_sha256'], row['source']
            modules = self.byprofile.setdefault(row['profile'], {})
            assert row['module'] not in modules, ('profile module collision', row['profile'], row['module'])
            modules[row['module']] = row
        self.visited = set()
        self.active = set()

    def paths(self, profile):
        names = PROFILE_ORDERS[profile]
        return [OUT / 'objects' / name for name in names] + self.external

    def dependencies(self, profile, modules):
        result = {}
        for module in modules:
            rel = Path(*module.split('.')).with_suffix('.olean')
            for directory in self.paths(profile) + [self.bin.parent / 'lib/lean']:
                obj = directory / rel
                if obj.is_file():
                    result[module] = {'sha256': digest(obj), 'path': str(obj)}
                    break
        assert len(result) == len(modules), ('missing compiled imports', profile, sorted(set(modules) - result.keys()))
        return result

    def provider_for(self, profile, module):
        order = PROFILE_ORDERS[profile]
        return next((self.byprofile[p][module] for p in order if module in self.byprofile.get(p, {})), None)

    def output(self, profile, module):
        return OUT / 'objects' / profile / Path(*module.split('.')).with_suffix('.olean')

    def latest(self, profile, module):
        return OUT / 'latest' / profile / Path(*module.split('.')).with_suffix('.json')

    def reusable(self, row):
        latest = self.latest(row['profile'], row['module'])
        output = self.output(row['profile'], row['module'])
        if not latest.is_file() or not output.is_file():
            return False
        receipt = read(latest)
        if receipt.get('compiler_binary_sha256') != self.compiler_binary_sha256:
            return False
        if not receipt['status'].startswith('PASS') or receipt['source_sha256'] != row['source_sha256']:
            return False
        if digest(output) != receipt['object_sha256'] or digest(ROOT / row['source']) != row['source_sha256']:
            return False
        now = self.dependencies(row['profile'], imports(ROOT / row['source']))
        return {k: v['sha256'] for k, v in now.items()} == receipt['direct_import_sha256']

    def compile(self, row):
        key = row['profile'] + ':' + row['module']
        if key in self.visited:
            return
        assert key not in self.active, ('source import cycle', key)
        self.active.add(key)
        for name in imports(ROOT / row['source']):
            provider = self.provider_for(row['profile'], name)
            if provider is not None:
                self.compile(provider)
        self.active.remove(key)
        if self.reusable(row):
            self.visited.add(key)
            print('REUSE_MATCHING_VERIFIED_ARTIFACT', key, flush=True)
            return
        memory = 6144 if key == 'base:ThetaCertificate5' else 4096
        limit = 600 if key == 'base:ThetaCertificate5' else 180
        self.invoke(row['profile'], row['module'], ROOT / row['source'],
                    row['source_sha256'], imports(ROOT / row['source']), memory, limit)
        self.visited.add(key)

    def invoke(self, profile, module, source, source_sha, module_imports, memory=4096, limit=180,
               audit_kind=None, selected=None):
        assert digest(source) == source_sha
        stamp = str(time.time_ns())
        destination = OUT / 'receipts' / profile / (module.replace('.', '_') + '-' + stamp)
        destination.mkdir(parents=True)
        rel = Path(*module.split('.')).with_suffix('.lean')
        frozen = destination / rel
        frozen.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, frozen)
        before = self.dependencies(profile, module_imports)
        obj = destination / rel.with_suffix('.olean')
        obj.parent.mkdir(parents=True, exist_ok=True)
        env = os.environ.copy()
        env['LEAN_PATH'] = ':'.join(str(p) for p in self.paths(profile))
        env['LEAN_NUM_THREADS'] = '1'
        command = ['timeout', str(limit), str(self.bin / 'lean'), '-j1', '-M' + str(memory)]
        if audit_kind is None:
            command += ['-o', str(obj)]
        command += [str(rel)]
        start = time.monotonic()
        with (destination / 'build.log').open('w') as log:
            result = subprocess.run(command, cwd=destination, env=env, stdout=log, stderr=subprocess.STDOUT)
        after = self.dependencies(profile, module_imports)
        stable = before == after and digest(source) == source_sha and digest(frozen) == source_sha
        text = (destination / 'build.log').read_text()
        lines = [' '.join(x.split()) for x in re.findall(r"'[^']+' depends on axioms: \[.*?\]|'[^']+' does not depend on any axioms", text, re.S)]
        bad = sorted({a.strip() for line in lines for a in re.findall(r'\[(.*?)\]', line)
                      for a in a.split(',') if a.strip() not in STANDARD})
        passed = result.returncode == 0 and stable and not bad
        receipt = {'status': 'PASS_FRESH_COMPONENT' if passed else 'FAILED_OR_CHANGED_ATTEMPT',
                   'profile': profile, 'module': module, 'source_sha256': source_sha,
                   'command': command, 'exit_code': result.returncode,
                   'elapsed_seconds': time.monotonic() - start,
                   'source_and_direct_imports_stable': stable,
                   'direct_import_sha256': {k: v['sha256'] for k, v in before.items()},
                   'compiler_commit': COMPILER, 'compiler_binary_sha256': self.compiler_binary_sha256,
                   'mathlib_commit': MATHLIB, 'memory_MiB': memory, 'timeout_seconds': limit,
                   'selected_axiom_lines': lines, 'nonstandard_selected_axioms': bad,
                   'log_sha256': digest(destination / 'build.log'),
                   'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   'full_master_or_scientific_applicability_inferred': False}
        if obj.is_file():
            receipt['object_sha256'] = digest(obj)
        if audit_kind:
            report = destination / 'declarations.json'
            if report.is_file():
                data = read(report)
                receipt.update(report_sha256=digest(report), declaration_count=data['declaration_count'])
                if audit_kind == 'axioms':
                    owned = [x['name'] for x in data['declarations'] if x['kind'] == 'axiom']
                    passed = passed and not owned and not data['missing_modules'] and not data['nonstandard_axiom_rows']
                    passed = passed and not any(set(x['axioms']) - STANDARD for x in data['declarations'])
                    receipt.update(theorem_declaration_count=data['theorem_declaration_count'],
                                   owned_axiom_declarations=owned, missing_modules=data['missing_modules'],
                                   nonstandard_axiom_rows=data['nonstandard_axiom_rows'])
                else:
                    receipt.update(owned_body_edges=sum(len(x['owned_body_references']) for x in data['declarations']),
                                   owned_type_edges=sum(len(x['owned_type_references']) for x in data['declarations']))
            else:
                passed = False
            receipt.update(status=('PASS_' if passed else 'FAILED_') + audit_kind.upper() + '_AUDIT', selected_modules=selected)
        save(destination / 'receipt.json', receipt)
        if not passed:
            print(text[-5000:], flush=True)
            raise RuntimeError('Failed attempt preserved: ' + str(destination))
        if audit_kind is None:
            target = self.output(profile, module)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(obj, target)
            receipt['receipt_path'] = str((destination / 'receipt.json').relative_to(ROOT))
            save(self.latest(profile, module), receipt)
        print(json.dumps({k: receipt.get(k) for k in ['status', 'profile', 'module', 'elapsed_seconds',
                                                     'declaration_count', 'theorem_declaration_count']}), flush=True)
        return destination

    def borrow(self, provider_directory):
        directory = Path(provider_directory).resolve()
        rows = read(directory / 'PROVIDERS-standard.json') + read(directory / 'PROVIDERS-ThetaCertificate5.json')
        copied = []
        for provider in rows:
            module = provider['module']
            row = self.byprofile['base'][module]
            src = directory / 'sources' / (module + '.lean')
            obj = directory / 'objects' / (module + '.olean')
            receipt_path = directory / provider['receipt']
            receipt = read(receipt_path)
            assert provider['status'] == receipt['status'] == 'PASS' and receipt['exit_code'] == 0
            assert provider['source_sha256'] == row['source_sha256'] == digest(src) == receipt['source_sha256']
            assert provider['object_sha256'] == digest(obj) == receipt['object_sha256']
            assert receipt['source_and_direct_imports_stable'] and not receipt['nonstandard_selected_axioms']
            assert receipt['compiler_binary_sha256'] == self.compiler_binary_sha256
            target = self.output('base', module)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(obj, target)
            saved = OUT / 'borrowed-providers' / module
            saved.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(receipt_path, saved / 'original-receipt.json')
            current = {**receipt, 'status': 'PASS_BORROWED_FRESH_VERIFIED_PROVIDER',
                       'profile': 'base', 'source_sha256': row['source_sha256'],
                       'direct_import_sha256': {k: v['sha256'] for k, v in receipt['direct_import_artifacts'].items()},
                       'borrowed_original_receipt_sha256': digest(receipt_path),
                       'borrowed_provider_source_object_hash_verified': True}
            save(self.latest('base', module), current)
            copied.append({'module': module, 'source_sha256': row['source_sha256'],
                           'object_sha256': digest(obj), 'original_receipt_sha256': digest(receipt_path)})
        save(OUT / 'BORROWED-PROVIDERS.json', copied)
        print(json.dumps({'borrowed_fresh_providers': len(copied), 'heavy_Theta5_not_recompiled': True}), flush=True)

    def stage(self, profile):
        for row in self.byprofile[profile].values():
            self.compile(row)

    def aggregate(self, profile):
        name = AGGREGATE_NAMES[profile]
        modules = ['UnifiedLean']
        for p in PROFILE_ORDERS[profile]:
            if profile == 'pure-induction-v2' and p == 'main': continue
            if p != 'base': modules += sorted(self.byprofile[p])
        modules = list(dict.fromkeys(modules))
        source = OUT / 'generated' / (name + '.lean')
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text('\n'.join('import ' + m for m in modules) + '\n')
        self.invoke(profile, name, source, digest(source), modules, limit=180)
        return name

    def selected(self, profile):
        names = set(m for p in PROFILE_ORDERS[profile]
                    if not (profile == 'pure-induction-v2' and p == 'main')
                    for m in self.byprofile[p])
        if profile == 'pure-induction-v2':
            pending = [row for p in PROFILE_ORDERS[profile] if p != 'main'
                       for row in self.byprofile[p].values()]
            seen = set()
            while pending:
                row = pending.pop()
                key = row['profile'] + ':' + row['module']
                if key in seen: continue
                seen.add(key)
                if row['profile'] == 'main': names.add(row['module'])
                for m in imports(ROOT / row['source']):
                    provider = self.provider_for(profile, m)
                    if provider is not None: pending.append(provider)
        return sorted(names)

    def audit(self, profile, kind):
        modules = self.selected(profile)
        source = OUT / 'generated' / (profile.replace('-', '_') + '_' + kind + 'Audit.lean')
        body = ROOT / 'checks' / ('AllDeclarationsTemplate.body' if kind == 'axioms' else 'DeclarationDependencies.body')
        header = '\n'.join('import ' + m for m in modules) + '\nimport Lean.Util.CollectAxioms\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let selected : Array String := #[' + ','.join(json.dumps(m) for m in modules) + ']\n  let reportFile : String := "declarations.json"\n  let progressFile : String := "progress.txt"\n'
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(header + body.read_text())
        # Complete combined environments include the large Theta proof corpus and
        # the independent probability/source corpus. This is an audit-only bound;
        # all original theorem compiler resource settings stay unchanged.
        memory = 6144 if profile in ['main','pure-induction-v2'] else 4096
        return self.invoke(profile, source.stem, source, digest(source), modules + ['Lean.Util.CollectAxioms'],
                           memory=memory, limit=600, audit_kind=kind, selected=modules)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('stage', choices=['borrow-providers'] + STAGES + ['all','audit'])
    parser.add_argument('--providers')
    parser.add_argument('--profile', choices=AUDITED_PROFILES, default='main')
    args = parser.parse_args()
    OUT.mkdir(parents=True, exist_ok=True)
    with (OUT / '.serial-build.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        b = Builder()
        if args.stage == 'borrow-providers':
            assert args.providers, 'Supply the verified provider handoff directory'
            b.borrow(args.providers)
        elif args.stage == 'audit':
            b.audit(args.profile, 'axioms')
            b.audit(args.profile, 'dependencies')
        else:
            stages = STAGES if args.stage == 'all' else [args.stage]
            for profile in stages:
                b.stage(profile)
                if profile not in ['graph-repair', 'theta']:
                    b.aggregate(profile)
                    b.audit(profile, 'axioms')
                    b.audit(profile, 'dependencies')

if __name__ == '__main__':
    main()
