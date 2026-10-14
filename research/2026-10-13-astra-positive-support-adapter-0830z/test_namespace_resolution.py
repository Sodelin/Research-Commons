"""Bounded synthetic path/authentication controls; no Lean invocation."""
import hashlib
import tempfile
import unittest
from pathlib import Path

import namespace_resolution as route


class NamespaceControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='astra-namespace-control-')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / 'sources'
        self.build = self.root / 'owned'
        self.repos = [self.root / 'external']
        self.ext = self.repos[0] / '.lake/build/lib/lean'
        self.ext.mkdir(parents=True)
        self.modules = [dict(module='Astra.Proof', sha256='labelled-synthetic-research')]
        self.rows = {}
        self.sources = {}
        for index in range(7):
            name = 'Mathlib.Fixture.M' + str(index)
            source = self.source / (name.replace('.', '/') + '.lean')
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_text('-- labelled synthetic source ' + str(index))
            target = self.ext / (name.replace('.', '/') + '.olean')
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(b'labelled synthetic object ' + str(index).encode())
            source_hash = route.digest(source)
            self.modules.append(dict(module=name, sha256=source_hash))
            self.sources[name] = dict(source=str(source), source_sha256=source_hash, target=str(target))
            self.rows[name] = dict(source_sha256=source_hash, receipt_sha256='synthetic-receipt',
                                   artifacts={str(target): route.digest(target)})
        self.env = dict(LEAN_PATH=str(self.ext), LEAN_SRC_PATH=str(self.source),
            LEAN_NUM_THREADS='1', LEAN_STACK_SIZE_KB='8192', LEAN_IMPORT_WORKERS='1',
            MIMALLOC_ARENA_RESERVE='16384', RAYON_NUM_THREADS='1')
        self.lean_bin = Path('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/bin')

    def bind(self):
        return route.bind_routes(self.modules, self.source, self.build, self.repos,
                                 self.env, self.rows, self.sources, self.lean_bin)

    def test_complete_external_route_and_binding(self):
        env, binding = self.bind()
        self.assertEqual(env['LEAN_PATH'], str(self.ext) + ':' + str(self.build))
        self.assertEqual(len(binding['selected_mathlib_equivalences']), 7)
        self.assertEqual(binding['selected_environment']['MALLOC_ARENA_MAX'], '1')
        self.assertNotEqual(route.binding_digest(binding), route.binding_digest(dict(binding, owned_root='changed')))

    def test_earlier_research_namespace_directory_refuses_even_without_exact_object(self):
        (self.ext / 'Astra').mkdir()
        self.assertFalse((self.ext / 'Astra/Proof.olean').exists())
        with self.assertRaisesRegex(ValueError, 'top namespace'):
            self.bind()

    def test_earlier_research_root_object_refuses(self):
        (self.ext / 'Astra.olean').write_bytes(b'synthetic collision')
        with self.assertRaisesRegex(ValueError, 'top namespace'):
            self.bind()

    def test_earlier_research_root_path_exists_even_if_directory_refuses(self):
        (self.ext / 'Astra.olean').mkdir()
        with self.assertRaisesRegex(ValueError, 'top namespace'):
            self.bind()

    def test_changed_object_refuses(self):
        Path(self.sources['Mathlib.Fixture.M0']['target']).write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError, 'artifact differs'):
            self.bind()

    def test_missing_object_refuses(self):
        Path(self.sources['Mathlib.Fixture.M0']['target']).unlink()
        with self.assertRaises(FileNotFoundError):
            self.bind()

    def test_changed_selected_source_refuses(self):
        self.modules[1]['sha256'] = 'wrong'
        with self.assertRaisesRegex(ValueError, 'source differs'):
            self.bind()

    def test_changed_external_order_refuses(self):
        self.env['LEAN_PATH'] = str(self.build) + ':' + str(self.ext)
        with self.assertRaisesRegex(ValueError, 'root order'):
            self.bind()

    def test_partial_earlier_mathlib_namespace_refuses(self):
        partial = self.root / 'partial'
        (partial / '.lake/build/lib/lean/Mathlib').mkdir(parents=True)
        self.repos.insert(0, partial)
        self.env['LEAN_PATH'] = str(partial / '.lake/build/lib/lean') + ':' + str(self.ext)
        with self.assertRaisesRegex(ValueError, 'external namespace route'):
            self.bind()


if __name__ == '__main__':
    print('NAMESPACE_HELPER_SHA256', route.digest(route.__file__), flush=True)
    print('TEST_SOURCE_SHA256', route.digest(__file__), flush=True)
    unittest.main()
