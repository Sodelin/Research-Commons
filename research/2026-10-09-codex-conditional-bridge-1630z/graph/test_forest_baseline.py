"""Authored regression and exact comparison with the inherited explicit engine."""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
import importlib.util
import io
import json
from math import comb
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "applications/practical-solver"))
from forest_baseline import ForestGraph, HermitianDilation, canonical_forest, count_polynomial, evaluate_request, root_count_probability

EXPLICIT_PATH = ROOT / "research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py"
spec = importlib.util.spec_from_file_location("reviewed_explicit_forest", EXPLICIT_PATH)
explicit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(explicit)


def shifted(f):
    return tuple(explicit.relabel(t, {i: i + 1 for i in range(6)}) for t in f)


def token_code(tokens, graph):
    value = 0
    for token in tokens + [0] * (graph.token_slots - len(tokens)):
        value = (value << graph.token_bits) | token
    return value


def legacy_encode(f, m):
    # Reviewed checker encoding, independently copied for format compatibility.
    def tree_tokens(t):
        return [t] if type(t) is int else [m + 1] + tree_tokens(t[0]) + tree_tokens(t[1]) + [m + 2]
    tokens = []
    for i, root in enumerate(f):
        if i:
            tokens.append(m + 3)
        tokens += tree_tokens(root)
    return token_code(tokens, ForestGraph(m))


class ForestBaselineTests(unittest.TestCase):
    counters = defaultdict(int)

    def test_explicit_probability_same_inputs(self):
        xs = (Fraction(1, 2), Fraction(2, 3), Fraction(1, 65536), Fraction(65535, 65536))
        for m in range(1, 7):
            graph = ForestGraph(m)
            for x in xs:
                law = explicit.edge_law(m, x)
                self.assertEqual(sum(law.values()), 1)
                mass = Fraction(0)
                for f, value in law.items():
                    actual = graph.probability(shifted(f), x)
                    self.assertEqual(actual, value, (m, x, f))
                    self.assertGreater(actual, 0)
                    mass += actual
                    self.counters["exact_explicit_coordinate_comparisons"] += 1
                self.assertEqual(mass, 1)
                for r in range(1, m + 1):
                    observed = sum(value for f, value in law.items() if len(f) == r)
                    self.assertEqual(root_count_probability(m, r, x), observed)
                    self.counters["root_count_normalizations"] += 1

    def test_boundary_diagnostics(self):
        for m in range(1, 6):
            graph = ForestGraph(m)
            for x in (0, 1):
                law = explicit.edge_law(m, Fraction(x))
                mass = 0
                for f in explicit.forests(tuple(range(m))):
                    p = graph.probability(shifted(f), x, allow_boundary=True)
                    self.assertEqual(p, law.get(f, 0))
                    mass += p
                self.assertEqual(mass, 1)
                with self.assertRaises(ValueError):
                    graph.probability(graph.singleton_forest, x)

    def test_histories_and_lazy_neighbors(self):
        expected_counts = (1, 2, 7, 37, 266, 2431)
        for m, expected in enumerate(expected_counts, 1):
            graph = ForestGraph(m)
            forests = tuple(shifted(f) for f in explicit.forests(tuple(range(m))))
            self.assertEqual(len(forests), expected)
            histories = defaultdict(int, {graph.singleton_forest: 1})
            reverse = defaultdict(set)
            for f in sorted(forests, key=lambda f: -len(f)):
                iterator = graph.forward_neighbors(f)
                self.assertIs(iter(iterator), iterator)
                neighbors = tuple(iterator)
                self.assertEqual(len(neighbors), comb(len(f), 2))
                self.assertEqual(len(set(neighbors)), len(neighbors))
                self.assertEqual(sum(v for _, v in graph.row_entries(f)), 0)
                for g in neighbors:
                    histories[g] += histories[f]
                    reverse[g].add(f)
                    self.assertEqual(graph.generator_entry(f, g), 1)
                    self.counters["forward_edges"] += 1
            for f in forests:
                self.assertEqual(graph.history_statistics(f).histories, histories[f])
                self.assertEqual(set(graph.reverse_neighbors(f)), reverse[f])
                self.counters["history_and_reverse_checks"] += 1
            # Split only top roots: internal descendants remain opaque.
            total_histories = 1
            for r in range(m, 0, -1):
                self.assertEqual(sum(histories[f] for f in forests if len(f) == r), total_histories)
                total_histories *= comb(r, 2)

    def test_encoding_matches_reviewed_format(self):
        for m in range(1, 7):
            graph = ForestGraph(m)
            codes = set()
            for raw in explicit.forests(tuple(range(m))):
                f = shifted(raw)
                code = graph.encode(f)
                self.assertEqual(code, legacy_encode(f, m))
                self.assertEqual(graph.decode(code), f)
                codes.add(code)
                self.counters["canonical_roundtrips"] += 1
            self.assertEqual(len(codes), len(explicit.forests(tuple(range(m)))))
        graph = ForestGraph(1)
        accepted = []
        for code in range(graph.code_count):
            try:
                accepted.append(graph.decode(code))
            except ValueError:
                pass
        self.assertEqual(accepted, [(1,)])

    def test_invalid_shape_and_codes(self):
        graph = ForestGraph(3)
        bad_forests = ((), (1,), (1, 2, 2), (1, 2, 4), (True, 2, 3), ([1, 2], 3),
                       ((2, 1), 3), (3, (1, 2)), ((1, 2, 3),), ((1,), 2, 3))
        for f in bad_forests:
            with self.assertRaises(ValueError):
                graph.encode(f)
        bad_tokens = ([1, 0, 2], [1, 2, 3], [1, 6], [4, 1, 2], [5, 1],
                      [4, 1, 5, 6, 2, 6, 3], [7], [4, 1, 2, 3, 5], [1, 6, 2, 6, 2])
        for tokens in bad_tokens:
            with self.assertRaises(ValueError):
                graph.decode(token_code(tokens, graph))
        for code in (-1, True, 1.5, graph.code_count):
            with self.assertRaises(ValueError):
                graph.decode(code)

    def test_exact_numeric_contract(self):
        graph = ForestGraph(2)
        for x in (0.5, True, "1/2"):
            with self.assertRaises(TypeError):
                graph.probability((1, 2), x)
        for x in (Fraction(-1, 2), Fraction(3, 2)):
            with self.assertRaises(ValueError):
                graph.probability((1, 2), x)
        for m in (0, -1, True, 2.0):
            with self.assertRaises(ValueError):
                ForestGraph(m)
        for r in (0, 4, True):
            with self.assertRaises(ValueError):
                count_polynomial(3, r)
        with self.assertRaises(TypeError):
            graph.probability((1, 2), Fraction(1, 2), allow_boundary=1)

    def test_canonical_constructor_and_deep_tree(self):
        self.assertEqual(canonical_forest((3, (2, 1))), ((1, 2), 3))
        with self.assertRaises(ValueError):
            canonical_forest(((1, 2), 1))
        with self.assertRaises(ValueError):
            canonical_forest((True,))
        # Iterative validation/encoding/history processing handles depth > Python
        # recursion limit. Avoid recursive tuple comparison/repr in this test.
        m = 2000
        tree = 1
        for label in range(2, m + 1):
            tree = (tree, label)
        graph = ForestGraph(m)
        f = (tree,)
        code = graph.encode(f)
        self.assertEqual(graph.encode(graph.decode(code)), code)
        self.assertEqual(graph.history_statistics(f).histories, 1)
        self.assertEqual(graph.generator_entry(f, graph.decode(code)), 0)
        graph = ForestGraph(m + 1)
        f = (tree, m + 1)
        g = next(graph.forward_neighbors(f))
        self.assertEqual(graph.generator_entry(f, graph.decode(graph.encode(g))), 1)

    def test_hermitian_orientation_symmetry_rounding(self):
        for m in range(1, 5):
            graph, dilation = ForestGraph(m), HermitianDilation(ForestGraph(m))
            forests = tuple(shifted(f) for f in explicit.forests(tuple(range(m))))
            rows = [layer * graph.code_count + graph.encode(f) for layer in (0, 1) for f in forests]
            for row in rows:
                entries = dict(dilation.nonzero_entries(row))
                self.assertLessEqual(len(entries), dilation.sparsity)
                for column, value in entries.items():
                    self.assertEqual(dilation.entry(column, row), value)
                    self.assertLessEqual(abs(value), 1)
                    for p in (0, 1, 8):
                        rounded = dilation.rounded_entry(row, column, p)
                        self.assertEqual(rounded, dilation.rounded_entry(column, row, p))
                        self.assertLess(abs(Fraction(rounded, 1 << p) - value), Fraction(1, 1 << p))
                    self.counters["hermitian_nonzero_symmetry_checks"] += 1
                for column in rows:
                    a, f = divmod(row, graph.code_count)
                    b, g = divmod(column, graph.code_count)
                    expected = Fraction(0)
                    if a != b and m >= 2:
                        ff, gg = graph.decode(f), graph.decode(g)
                        expected = Fraction(graph.generator_entry(ff, gg) if a == 0 else graph.generator_entry(gg, ff), comb(m, 2))
                    self.assertEqual(dilation.entry(row, column), expected)

    def test_padded_location_full_register_inverse(self):
        rng = random.Random(20261009)
        for m in range(1, 6):
            graph = ForestGraph(m)
            dilation = HermitianDilation(graph)
            forests = tuple(shifted(f) for f in explicit.forests(tuple(range(m))))
            for layer in (0, 1):
                for f in forests:
                    row = layer * graph.code_count + graph.encode(f)
                    columns = dilation.padded_columns(row)
                    self.assertEqual(len(columns), dilation.sparsity)
                    self.assertEqual(len(set(columns)), dilation.sparsity)
                    self.assertTrue(set(c for c, _ in dilation.nonzero_entries(row)) <= set(columns))
                    probes = set(range(dilation.sparsity + 3)) | set(columns) | {dilation.index_count - 1}
                    probes.update(rng.randrange(dilation.index_count) for _ in range(4))
                    for value in probes:
                        self.assertEqual(dilation.inverse_location(row, dilation.location(row, value)), value)
                        self.assertEqual(dilation.location(row, dilation.inverse_location(row, value)), value)
                        self.counters["location_two_sided_inverse_probes"] += 1
            for invalid_row in (0, graph.code_count, dilation.index_count - 1):
                self.assertEqual(tuple(dilation.nonzero_entries(invalid_row)), ())
                self.assertEqual(dilation.entry(invalid_row, graph.encode(graph.singleton_forest)), 0)
                for value in (0, dilation.sparsity, dilation.index_count - 1):
                    self.assertEqual(dilation.inverse_location(invalid_row, dilation.location(invalid_row, value)), value)
        dilation = HermitianDilation(ForestGraph(1))
        row = dilation.graph.encode((1,))
        for value in range(dilation.index_count):
            self.assertEqual(dilation.location(row, dilation.inverse_location(row, value)), value)

    def test_bounded_request_contract(self):
        request = json.loads((Path(__file__).parent / "examples/one-ordinary-population.json").read_text())
        result = evaluate_request(request)
        self.assertEqual(result["status"], "EXACT_CLASSICAL_COORDINATE")
        p = result["probability"]
        self.assertEqual(Fraction(int(p["numerator_hex"], 16), int(p["denominator_hex"], 16)), Fraction(7, 192))
        self.assertFalse(result["source_witness"])
        self.assertFalse(result["quantum_advantage_established"])
        for altered in (dict(request, m=10**100), dict(request, extra=True), dict(request, m=True),
                        dict(request, forest=[[2, 1], 3, 4]), dict(request, survival={"numerator": 1, "denominator": 1}),
                        dict(request, survival={"numerator": 1.0, "denominator": 2}),
                        dict(request, survival={"numerator": 1, "denominator": 1 << 256})):
            with self.assertRaises((ValueError, TypeError)):
                evaluate_request(altered)

    def test_cli_semantic_success_and_refusals(self):
        script = ROOT / "applications/practical-solver/forest_baseline.py"
        request_path = Path(__file__).parent / "examples/one-ordinary-population.json"
        with tempfile.TemporaryDirectory() as directory:
            temp = Path(directory)
            command = [sys.executable, str(script), "--request", str(request_path), "--output", str(temp / "success")]
            run = subprocess.run(command, capture_output=True, text=True, timeout=10)
            self.assertEqual(run.returncode, 0, run.stderr)
            result = json.loads((temp / "success/RESULT.json").read_text())
            self.assertEqual(result["probability_display"], "7/192")
            self.assertIn("different evolution", (temp / "success/REPORT.md").read_text())
            before = (temp / "success/RESULT.json").read_bytes()
            repeat = subprocess.run(command, capture_output=True, text=True, timeout=10)
            self.assertEqual(repeat.returncode, 2)
            self.assertEqual((temp / "success/RESULT.json").read_bytes(), before)
            symlink = temp / "linked-request.json"
            symlink.symlink_to(request_path)
            linked = subprocess.run([sys.executable, str(script), "--request", str(symlink), "--output", str(temp / "linked-output")],
                                    capture_output=True, text=True, timeout=10)
            self.assertEqual(linked.returncode, 2)
            self.assertFalse((temp / "linked-output").exists())
            for index, text in enumerate((request_path.read_text().replace('"m": 4', '"m": 4, "m": 5'),
                                          request_path.read_text().replace('"numerator": 1', '"numerator": 1.0'),
                                          request_path.read_text().replace('"denominator": 2', '"denominator": 1'))):
                bad_path = temp / f"bad-{index}.json"
                bad_path.write_text(text)
                output = temp / f"refused-{index}"
                refusal = subprocess.run([sys.executable, str(script), "--request", str(bad_path), "--output", str(output)],
                                         capture_output=True, text=True, timeout=10)
                self.assertEqual(refusal.returncode, 2)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    stream = io.StringIO()
    result = unittest.TextTestRunner(stream=stream, verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(ForestBaselineTests))
    print(json.dumps({"status": "PASS" if result.wasSuccessful() else "FAIL", "evidence_tier": "authored_execution",
                      "tests_run": result.testsRun, "failures": len(result.failures), "errors": len(result.errors),
                      "exact_scope": "One ordinary population; explicit law comparisons m<=6; dilation matrix entries m<=4; location probes m<=5; no quantum circuits/simulator or Lean execution.",
                      "counters": dict(sorted(ForestBaselineTests.counters.items())), "unittest_log": stream.getvalue()}, indent=2))
    sys.exit(not result.wasSuccessful())
