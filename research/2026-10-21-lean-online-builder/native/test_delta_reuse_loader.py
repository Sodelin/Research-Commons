"""RAM-only policy and source-condition regressions; no native builder imports."""
import ast
import hashlib
import json
import re
from pathlib import Path
import unittest

from delta_reuse_loader import profile_for, invocation_allowed, SCRIPTS

HERE = Path(__file__).resolve().parent
PUBLIC = HERE.parent


def expression(node, values):
    return eval(compile(ast.Expression(node), '<retained-condition>', 'eval'), {}, values)


class FakePath:
    def __init__(self, value, dirs, files):
        self.value, self.dirs, self.files = value, dirs, files

    def __truediv__(self, part):
        return FakePath(self.value+'/'+part, self.dirs, self.files)

    def is_dir(self):
        return self.value in self.dirs

    def exists(self):
        return self.value in self.files or self.is_dir()


class ReuseTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.graph = (HERE/'physical-pmf/DEPENDENCY-GRAPH.json').read_bytes()
        cls.selection = (HERE/'physical-pmf/SOURCE-SELECTION.json').read_bytes()
        cls.template = (HERE/'pinned/AuditTemplate.lean').read_bytes()
        cls.profile = profile_for(cls.graph, cls.selection, cls.template)
        cls.modules = json.loads(cls.graph)['targets'][cls.profile['label']]['modules']
        cls.core = ast.parse((HERE/'retained-loader/build_connected.py').read_text())
        cls.previous = ast.parse((HERE/'pinned/build_connected.py').read_text())
        tree = ast.parse((HERE/'retained-loader/build_with_mathlib_overlay.py').read_text())
        lookup = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'lean_lookup')
        namespace = {}
        exec(compile(ast.Module(body=[lookup], type_ignores=[]), '<retained-lookup>', 'exec'), namespace)
        cls.lookup = staticmethod(namespace['lean_lookup'])

    def test_exact_role_partition(self):
        self.assertEqual((len(self.profile['original']), len(self.profile['added']),
                          len(self.profile['owned_mathlib'])), (755, 23, 10))

    def test_changed_graph_refused(self):
        with self.assertRaises(ValueError):
            profile_for(self.graph+b' ', self.selection, self.template)

    def test_changed_selection_refused(self):
        with self.assertRaises(ValueError):
            profile_for(self.graph, self.selection+b' ', self.template)

    def test_changed_audit_template_refused(self):
        with self.assertRaises(ValueError):
            profile_for(self.graph, self.selection, self.template+b' ')

    def test_every_original_fresh_invocation_refused(self):
        for name in self.profile['original']:
            self.assertFalse(invocation_allowed(self.profile, name, self.modules[name]['sha256'],
                                               True, 180, 4096, 'component'))

    def test_unknown_component_never_matches_absence(self):
        for source in [None, '0'*64]:
            self.assertFalse(invocation_allowed(self.profile, 'AbsentModule', source,
                                               True, 180, 4096, 'component'))

    def test_every_delta_exact_source_and_changed_source(self):
        for name, source in self.profile['added'].items():
            self.assertTrue(invocation_allowed(self.profile, name, source,
                                              True, 180, 4096, 'component'))
            self.assertFalse(invocation_allowed(self.profile, name, '0'*64,
                                               True, 180, 4096, 'component'))

    def test_delta_caps_and_output_mode(self):
        name, source = next(iter(self.profile['added'].items()))
        for obj, seconds, memory, kind in [(False, 180, 4096, 'component'),
                                          (True, 600, 4096, 'component'),
                                          (True, 180, 6144, 'component'),
                                          (True, 180, 4096, 'unknown')]:
            self.assertFalse(invocation_allowed(self.profile, name, source,
                                               obj, seconds, memory, kind))

    def test_aggregate_exact_document(self):
        p = self.profile
        self.assertTrue(invocation_allowed(p, p['aggregate_name'], p['aggregate_sha256'],
                                          True, 180, 4096, 'aggregate'))
        self.assertFalse(invocation_allowed(p, p['aggregate_name'], '0'*64,
                                           True, 180, 4096, 'aggregate'))
        self.assertFalse(invocation_allowed(p, 'Connected_other', p['aggregate_sha256'],
                                           True, 180, 4096, 'aggregate'))

    def test_aggregate_name_matches_actual_retained_core(self):
        safe = next(n for n in self.core.body if isinstance(n, ast.FunctionDef) and n.name == 'safe')
        namespace = {'re': re}
        exec(compile(ast.Module(body=[safe], type_ignores=[]), '<retained-safe>', 'exec'), namespace)
        self.assertEqual(self.profile['aggregate_name'], 'Connected_'+namespace['safe'](self.profile['label']))

    def test_audit_exact_document_and_no_object(self):
        p = self.profile
        self.assertTrue(invocation_allowed(p, 'OwnedAudit', p['audit_sha256'],
                                          False, 180, 4096, 'complete-owned-audit'))
        self.assertFalse(invocation_allowed(p, 'OwnedAudit', '0'*64,
                                           False, 180, 4096, 'complete-owned-audit'))
        self.assertFalse(invocation_allowed(p, 'OwnedAudit', p['audit_sha256'],
                                           True, 180, 4096, 'complete-owned-audit'))

    def test_partial_namespace_does_not_fall_through(self):
        dirs = {'context/Mathlib', 'external/Mathlib'}
        files = {'external/Mathlib/Tactic/Ring.olean'}
        roots = [FakePath('context', dirs, files), FakePath('external', dirs, files)]
        found = self.lookup(roots, 'Mathlib.Tactic.Ring')
        self.assertEqual(found.value, 'context/Mathlib/Tactic/Ring.olean')
        self.assertFalse(found.exists())
        self.assertTrue((roots[1]/'Mathlib/Tactic/Ring.olean').exists())

    def test_lookup_without_partial_namespace(self):
        dirs, files = {'external/Mathlib'}, {'external/Mathlib/Tactic/Ring.olean'}
        roots = [FakePath('context', dirs, files), FakePath('external', dirs, files)]
        self.assertEqual(self.lookup(roots, 'Mathlib.Tactic.Ring').value,
                         'external/Mathlib/Tactic/Ring.olean')

    def test_zero_exit_failed_audit_status_is_rejected(self):
        strict = next(n.test for n in ast.walk(self.core) if isinstance(n, ast.If)
                      and ast.unparse(n.test) == "ar['status'] != 'PASS_FRESH_KERNEL_CHECK'")
        weak = next(n.test for n in ast.walk(self.previous) if isinstance(n, ast.If)
                    and ast.unparse(n.test) == "ar['exit_code'] != 0")
        values = {'ar': {'status': 'FAILED_OR_RESOURCE', 'exit_code': 0}}
        self.assertTrue(expression(strict, values))
        self.assertFalse(expression(weak, values))

    def test_compiler_drift_prevents_final_acceptance(self):
        def ok(tree):
            return next(n.value for n in ast.walk(tree) if isinstance(n, ast.Assign)
                        and any(isinstance(t, ast.Name) and t.id == 'ok' for t in n.targets))
        values = {'self': type('Result', (), {'results': [{'status': 'PASS'}]})(),
                  'native_final_stable': True, 'compiler_final_stable': False}
        self.assertFalse(expression(ok(self.core), values))
        self.assertTrue(expression(ok(self.previous), values))

    def test_retained_sources_byte_exact(self):
        for name, wanted in SCRIPTS.items():
            self.assertEqual(hashlib.sha256((HERE/'retained-loader'/name).read_bytes()).hexdigest(), wanted)


if __name__ == '__main__':
    unittest.main()
