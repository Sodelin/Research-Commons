#!/usr/bin/env python3
# Codex / lean_integration_successor: exact pinned four-module namespace and storage adapter.
"""Isolated Mathlib namespace completion around the unchanged strict builder.
No compiler flags, cache checks, proof sources or audit conditions are changed.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, shutil
ROOT = Path(__file__).resolve().parents[1]
CORE_SHA = '13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc'
FINENUM_SHA = '381c6f445637fdf6bc04a77f062ed2079d9856eeb260b30b609f3c098a3e430a'
OWNED_MATHLIB = {'Mathlib.Data.FinEnum': '381c6f445637fdf6bc04a77f062ed2079d9856eeb260b30b609f3c098a3e430a', 'Mathlib.Algebra.MvPolynomial.Polynomial': '43330a5e928a56af89b209101f98be347937384d2d435f875e2eaff698ccd650', 'Mathlib.Algebra.MvPolynomial.Funext': 'cb1821884a139917b692103a0b267115179cd4e7084da5487857ec49abb0cc7e', 'Mathlib.Analysis.Convex.Caratheodory': '8e2ead25535366604c2caab3071e5549586f909fe70b885d1c75784e117720f2'}
CACHE_INSTALL_MANIFEST_SHA = '65e6a3e66bbaadb5a569c2cf7ef8dc205f1b75f3c5150fc7608261d01e5758e3'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
core_path = ROOT / 'scripts/build_connected.py'
assert sha(core_path) == CORE_SHA
spec = importlib.util.spec_from_file_location('unchanged_connected_builder', core_path)
core = importlib.util.module_from_spec(spec)
spec.loader.exec_module(core)


def lean_lookup(roots, module):
    """Literal Lean.Util.Path.SearchPath.findWithExt rule for olean files."""
    package = module.split('.')[0]
    for root in roots:
        if (root / package).is_dir() or (root / (package + '.olean')).exists():
            return root / (module.replace('.', '/') + '.olean')
    raise RuntimeError('Lean package namespace absent: ' + module)


def overlay_mathlib(source_root, context):
    """Real ancestors for exactly four owned original modules; symlink siblings."""
    source = source_root / 'Mathlib'
    assert source.is_dir()
    protected = tuple(tuple(m.split('.')[1:]) for m in sorted(OWNED_MATHLIB))
    links = []

    def stage(src, dst, parts):
        assert not dst.is_symlink(), ('Owned ancestor must be real', dst)
        dst.mkdir(exist_ok=True, parents=True)
        for child in sorted(src.iterdir()):
            rel = parts + (child.name,)
            out = dst / child.name
            if child.is_dir() and any(rel == p[:len(rel)] for p in protected):
                stage(child, out, rel)
            elif any(parts == p[:-1] and
                     (child.name == p[-1] or child.name.startswith(p[-1] + '.'))
                     for p in protected):
                raise RuntimeError('Unexpected external owned artifact: ' + str(child))
            else:
                target = child.resolve(strict=True)
                if out.is_symlink():
                    assert out.resolve(strict=True) == target, ('Overlay target drift', out)
                elif out.exists():
                    raise RuntimeError('Refusing to replace existing overlay path: ' + str(out))
                else:
                    out.symlink_to(target, target_is_directory=child.is_dir())
                links.append({'relative': str(Path('Mathlib', *rel)),
                              'target': str(target), 'directory': child.is_dir()})

    stage(source, context / 'Mathlib', ())
    for parts in protected:
        ancestor = context / 'Mathlib'
        for name in parts[:-1]:
            ancestor = ancestor / name
            assert not ancestor.is_symlink(), ('Owned ancestor must be real', ancestor)
            ancestor.mkdir(exist_ok=True)
    return links


class OverlayBuilder(core.Builder):
    def __init__(self):
        super().__init__()
        owned = {m: e['sha256'] for t in self.graph['targets'].values()
                 for m, e in t['modules'].items() if m.startswith('Mathlib.')}
        assert owned == OWNED_MATHLIB
        self.overlay_contexts = {}
        self.overlay_external = self.mathlib / '.lake/build/lib/lean'
        self.resolutions = self.run / 'NAMESPACE-RESOLUTION-CHECKS.jsonl'
        shutil.copy2(Path(__file__), self.run / 'NAMESPACE-OVERLAY-WRAPPER.py')
        core.save(self.run / 'NAMESPACE-OVERLAY-PINS.json', {
            'wrapper_sha256': sha(Path(__file__)), 'core_builder_sha256': sha(core_path),
            'graph_sha256': self.graph_sha, 'mathlib_commit': core.MATHLIB,
            'official_owned_module': owned, 'external_object_root': str(self.overlay_external),
            'lookup_rule_source': str(self.bin.parent / 'src/lean/Lean/Util/Path.lean'),
            'lookup_rule_source_sha256': sha(self.bin.parent / 'src/lean/Lean/Util/Path.lean'),
            'prior_attempt_reference': str(ROOT / 'STAGING-PROVENANCE.json'),
            'artifact_binding': 'Unchanged core hashes direct imported bundles before/after each attempt; successful full owned audit records all actually imported module bundles. This wrapper also pins every overlay symlink target and checks actual Lean first-namespace resolution.'})

    def install(self, base, out, expected):
        """Verify original inputs, then hard-link an exact staged local alias."""
        import errno
        original_base = base
        assert core.artifact_bundle(original_base) == expected, ('Original companion drift', original_base)
        manifest_path = ROOT / 'CACHE-INSTALL-ALIASES.json'
        assert sha(manifest_path) == CACHE_INSTALL_MANIFEST_SHA, 'Install manifest drift'
        if not hasattr(self, 'cache_install_aliases'):
            manifest = core.read(manifest_path)
            assert manifest['workspace'] == str(ROOT) and manifest['graph_sha256'] == self.graph_sha
            self.cache_install_aliases = {entry['original_cached_object']: entry for entry in manifest['entries']}
            assert len(self.cache_install_aliases) == len(manifest['entries'])
            shutil.copyfile(manifest_path, self.run / 'CACHE-INSTALL-ALIASES.json')
            core.save(self.run / 'CACHE-INSTALL-TRANSPORT-PINS.json', {
                'manifest_sha256': CACHE_INSTALL_MANIFEST_SHA,
                'derivation_sha256': sha(ROOT / 'CACHE-INSTALL-TRANSPORT-DERIVATION.json'),
                'original_receipt_paths_and_bytes_unchanged': True,
                'original_and_staged_companions_verified_before_and_after_install': True,
                'core_builder_sha256': sha(core_path),
                'compiler_flags_caps_cache_keys_and_audit_unchanged': True})
        entry = self.cache_install_aliases.get(str(original_base))
        if entry is not None:
            assert entry['object_artifacts'] == expected
            receipt = Path(entry['original_receipt'])
            staged_receipt = Path(entry['staged_receipt'])
            assert sha(receipt) == sha(staged_receipt) == entry['receipt_sha256'], 'Receipt drift'
            rec = core.read(receipt)
            assert rec['cached_object'] == str(original_base) and rec['object_artifacts'] == expected
            base = Path(entry['staged_cached_object'])
            assert base.is_relative_to(self.cache) and base.parent.name == entry['cache_key']
            assert core.artifact_bundle(base) == expected, ('Staged companion drift', base)
        assert out.is_relative_to(self.run), ('Install destination outside fresh run', out)
        out.parent.mkdir(parents=True, exist_ok=True)
        transports = []
        for suffix in core.SUFFIXES:
            source, destination = core.companion(base, suffix), core.companion(out, suffix)
            if source.exists():
                assert sha(source) == expected[suffix]
                if destination.exists():
                    assert sha(destination) == sha(source), ('Existing context artifact differs', destination)
                    mode = 'VERIFIED_EXISTING_DESTINATION'
                else:
                    try:
                        os.link(source, destination)
                        mode = 'SAME_FILESYSTEM_HARD_LINK'
                        assert (source.stat().st_dev, source.stat().st_ino) == (destination.stat().st_dev, destination.stat().st_ino)
                    except OSError as error:
                        if error.errno != errno.EXDEV:
                            raise
                        shutil.copy2(source, destination)
                        mode = 'EXDEV_HASH_CHECKED_COPY2'
                assert sha(destination) == sha(source) == expected[suffix]
                transports.append({'suffix': suffix, 'source': str(source), 'destination': str(destination),
                    'sha256': expected[suffix], 'bytes': source.stat().st_size, 'transport': mode,
                    'source_device_inode': [source.stat().st_dev, source.stat().st_ino],
                    'destination_device_inode': [destination.stat().st_dev, destination.stat().st_ino]})
        assert core.artifact_bundle(original_base) == expected, ('Original changed during install', original_base)
        assert core.artifact_bundle(base) == expected, ('Staged changed during install', base)
        assert core.artifact_bundle(out) == expected, ('Installed companion drift', out)
        if entry is not None:
            assert sha(Path(entry['original_receipt'])) == sha(Path(entry['staged_receipt'])) == entry['receipt_sha256']
        with (self.run / 'CACHE-INSTALL-TRANSPORT-CHECKS.jsonl').open('a') as stream:
            stream.write(json.dumps({'original_object': str(original_base), 'install_source': str(base),
                'destination': str(out), 'cache_key': entry['cache_key'] if entry is not None else None,
                'object_artifacts': expected, 'original_and_staged_pre_post_checks_pass': True,
                'files': transports}, sort_keys=True) + '\n')

    def dependencies(self, context, modules):
        links = overlay_mathlib(self.overlay_external, context)
        if context not in self.overlay_contexts:
            self.overlay_contexts[context] = links
            core.save(context.parent / 'MATHLIB-NAMESPACE-OVERLAY.json', links)
        else:
            assert self.overlay_contexts[context] == links, 'Overlay symlink inventory drift'
        result = super().dependencies(context, modules)
        checked = {}
        for module, measured in result.items():
            actual = lean_lookup([context] + self.external, module)
            assert actual.is_file(), ('Lean-selected module is absent', module, actual)
            assert actual.resolve() == Path(measured['path']).resolve(), (
                'Measured import differs from Lean namespace resolution', module, actual, measured['path'])
            assert core.artifact_bundle(actual) == measured['artifacts']
            checked[module] = {'lean_path': str(actual), 'resolved_target': str(actual.resolve()),
                               'artifacts': measured['artifacts']}
        with self.resolutions.open('a') as stream:
            stream.write(json.dumps({'context': str(context), 'imports': checked}, sort_keys=True) + '\n')
        return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('target', choices=list(core.read(ROOT / 'DEPENDENCY-GRAPH.json')['targets']))
    args = parser.parse_args()
    builder = OverlayBuilder()
    raise SystemExit(builder.run_targets([args.target]))
