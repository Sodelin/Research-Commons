#!/usr/bin/env python3
"""Transport one supplied legacy fitter witness; launch no scientific engine.

The exact Fraction/whitelisted-AST predecessor is the preserved
evidence/source-fit-bank-bridge-1/capture.py (7657508b...). This module selects
a panel explicitly, retains every supplied equation and preserves raw origin
bytes. Supplied status/digests are representation bindings, not independent
source admission, equation provenance, observation fit or native refinement.
"""
from __future__ import annotations

import argparse
import ast
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import re
import sys

MAX_ORIGIN_BYTES = 16 * 1024 * 1024
MAX_REQUEST_BYTES = 65536
MAX_SIDECAR_BYTES = MAX_ORIGIN_BYTES + 4 * MAX_REQUEST_BYTES
MAX_JSON_DEPTH = 128
MAX_JSON_NODES = 262144
MAX_AST_NODES = 4096
MAX_AST_BYTES = 65536
MAX_AST_POWER = 64  # Retains the audited predecessor's expression sublanguage.
HARD_RATIONAL_BITS = 65536
U64_MAX = (1 << 64) - 1
DEFAULT_LIMITS = {"equations": 4096, "terms": 65536,
    "arithmetic_steps": 1000000, "rational_bits": 4096, "power_exponent": 4096}
HARD_LIMITS = {**DEFAULT_LIMITS, "rational_bits": HARD_RATIONAL_BITS}
COMPILER_LIMITS = {"word_length": 32, "slots": 16, "variables": 256}
CONTRACT_PINS = {
    "FITTER-WITNESS-TRANSPORT-20261010T2240Z.md":
        "7d5bd1382178511a13b6728a59fdc482ef4a6a5d810939f85ce6423111c83782",
    "FITTER-WITNESS-TRANSPORT-CORRECTION-20261010T2241Z.md":
        "09d5df2fadfd21d9c3c1af4de9cf1f05fb8428cd545b479be0337ae7df9af8e1",
    "predecessor_capture.py":
        "7657508bc0147c5bb16039612b5a4a0e1d7c7741236868e319dafc8da2ff645b",
    "legacy_solver.py":
        "42e4353d3033e807e26bc409c724fcdee2a01552a630c9364f428f92f9ffe0db",
}
SCIENCE_FALSE = ("certificate_valid", "source_admission_verified",
    "source_equation_provenance_verified", "source_observation_fit_verified",
    "source_provenance_verified", "selected_experiment_reproduced",
    "timed_readout_verified", "universal_native_refinement_verified",
    "full_solver_verified", "statistical_confidence_verified",
    "unknown_size_exclusion_verified", "provider_work_checked",
    "provider_exhaustion_verified")
RESULT_SCHEMA = "actual-finite-original-registry-coupled-source-solver-v1"
RESULT_REQUIRED = {"schema", "request", "request_sha256", "upstream", "software",
    "unknown_size_termination_or_global_NO_claimed", "Lean_verification_claimed",
    "empirical_admission_claimed", "status", "verification", "scope",
    "source_count_examined", "catalogue_exhausted", "entries", "witness_entry",
    "elapsed_seconds"}
ENTRY_REQUIRED = {"graph", "mechanism", "equations", "equation_sha256", "target",
    "query", "query_sha256", "status", "values", "physical_realization"}
REQUEST_ALLOWED = {"observation_kind", "clock_contract", "n", "registry",
    "mechanisms", "taxa", "task", "target_kind", "limits", "rows",
    "empirical_admission"}
ROW_ALLOWED = {"samples", "forced", "program", "readout", "quartets", "law"}
FLOAT_PATHS = {("elapsed_seconds",), ("request", "limits", "seconds")}
HEX = re.compile(r"[0-9a-f]{64}\Z")
INTEGER = re.compile(r"[+-]?[0-9]+\Z")
RATIO = re.compile(r"([+-]?[0-9]+)/([+-]?[0-9]+)\Z")
DECIMAL = re.compile(r"([+-]?)(?:([0-9]+)(?:\.([0-9]*))?|\.([0-9]+))(?:[eE]([+-]?[0-9]+))?\Z")


class TransportError(ValueError):
    def __init__(self, status, code, detail, limit=None):
        super().__init__(detail)
        self.status, self.code, self.detail, self.limit = status, code, detail, limit


def refuse(code, detail):
    raise TransportError("INVALID_REQUEST", code, detail)


def unsupported(code, detail):
    raise TransportError("UNSUPPORTED", code, detail)


def cap(kind, required, limit, stage="TRANSPORT"):
    if required > limit:
        raise TransportError("UNKNOWN", "TRANSPORT_RESOURCE_LIMIT",
            "Transport resource bound exceeded; no native request produced.",
            {"stage": stage, "kind": kind, "required": required, "cap": limit})


def require(condition, code, detail):
    if not condition:
        refuse(code, detail)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def integer_text(value):
    """Exact decimal rendering without changing Python's global digit policy."""
    if not value:
        return "0"
    sign, value = ("-", -value) if value < 0 else ("", value)
    chunks = []
    while value:
        value, part = divmod(value, 1000000000)
        chunks.append(part)
    return sign + str(chunks[-1]) + "".join(f"{p:09d}" for p in reversed(chunks[:-1]))


def decimal_integer(token):
    digits = token.lstrip("+-")
    # 19730 decimal digits already exceed any allowed 65536-bit operand.
    cap("integer_digits", len(digits), 19730, "JSON")
    value = 0
    for start in range(0, len(digits), 9):
        chunk = digits[start:start + 9]
        value = value * (10 ** len(chunk)) + int(chunk)
        cap("integer_bits", value.bit_length(), HARD_RATIONAL_BITS, "JSON")
    return -value if token.startswith("-") else value


def canonical_bytes(value, bound=MAX_SIDECAR_BYTES, newline=False):
    """Inherited sorted/compact/ASCII JSON, including finite metadata floats."""
    chunks, length = [], 0

    def emit(text):
        nonlocal length
        length += len(text)
        cap("serialized_bytes", length + int(newline), bound, "FRAME")
        chunks.append(text)

    def visit(item, depth=0):
        cap("json_depth", depth, MAX_JSON_DEPTH, "FRAME")
        if item is None:
            emit("null")
        elif type(item) is bool:
            emit("true" if item else "false")
        elif type(item) is int:
            emit(integer_text(item))
        elif type(item) is float:
            require(math.isfinite(item), "NONFINITE", "Nonfinite JSON metadata is forbidden.")
            emit(json.dumps(item, allow_nan=False))
        elif type(item) is str:
            emit(json.dumps(item, ensure_ascii=True))
        elif type(item) is list:
            emit("[")
            for index, child in enumerate(item):
                if index:
                    emit(",")
                visit(child, depth + 1)
            emit("]")
        elif type(item) is dict:
            require(all(type(key) is str for key in item), "JSON_KEYS", "Object keys must be strings.")
            emit("{")
            for index, key in enumerate(sorted(item)):
                if index:
                    emit(",")
                emit(json.dumps(key, ensure_ascii=True)); emit(":")
                visit(item[key], depth + 1)
            emit("}")
        else:
            refuse("JSON_TYPE", "Non-JSON value in transport.")

    visit(value)
    if newline:
        chunks.append("\n")
    return "".join(chunks).encode("ascii")


def parse_backend(raw):
    require(type(raw) is bytes, "RAW_BYTES", "Supply the exact backend RESULT.json bytes.")
    cap("origin_bytes", len(raw), MAX_ORIGIN_BYTES, "INPUT")
    # Preflight nesting before the recursive standard-library JSON decoder.
    depth, quoted, escaped = 0, False, False
    for byte in raw:
        if quoted:
            if escaped:
                escaped = False
            elif byte == 92:
                escaped = True
            elif byte == 34:
                quoted = False
        elif byte == 34:
            quoted = True
        elif byte in (91, 123):
            depth += 1
            cap("json_depth", depth, MAX_JSON_DEPTH, "INPUT")
        elif byte in (93, 125):
            depth -= 1

    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "DUPLICATE_KEY", "Duplicate JSON object key.")
            result[key] = value
        return result

    def constant(_):
        refuse("NONFINITE", "Nonfinite JSON numbers are forbidden.")

    try:
        result = json.loads(raw.decode("utf-8"), object_pairs_hook=pairs,
            parse_int=decimal_integer, parse_constant=constant)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as error:
        refuse("BACKEND_JSON", "Invalid bounded UTF-8 backend JSON: " + str(error)[:160])
    nodes, stack = 0, [((), result)]
    while stack:
        path, item = stack.pop()
        nodes += 1
        cap("json_nodes", nodes, MAX_JSON_NODES, "INPUT")
        if type(item) is float:
            require(path in FLOAT_PATHS and math.isfinite(item), "FLOAT_PATH",
                "Finite floats are allowed only in elapsed_seconds and request.limits.seconds.")
        elif type(item) is dict:
            stack.extend((path + (key,), child) for key, child in item.items())
        elif type(item) is list:
            stack.extend((path + (index,), child) for index, child in enumerate(item))
    return result


def object_fields(value, required, allowed, code):
    require(type(value) is dict, code, "Expected a JSON object.")
    require(required <= set(value), code, "Required object fields are missing.")
    if set(value) - allowed:
        unsupported(code, "Unreviewed object fields: " + ", ".join(sorted(set(value) - allowed)))


def natural(value, code, maximum=U64_MAX):
    require(type(value) is int and 0 <= value <= maximum, code, "Expected a bounded nonnegative integer.")
    return value


def label(value, code):
    require(type(value) is str and value and "\0" not in value, code, "Expected a nonempty label without NUL.")
    try:
        require(len(value.encode("utf-8")) <= 128, code, "Label exceeds the inherited native 128-byte bound.")
    except UnicodeError:
        refuse(code, "Label is not valid UTF-8.")
    return value


def label_list(value, code):
    require(type(value) is list, code, "Expected a label list.")
    result = [label(item, code) for item in value]
    require(len(set(result)) == len(result), code, "Labels must be distinct.")
    return result


class Arithmetic:
    def __init__(self, limits):
        self.limits, self.steps = limits, 0

    def checked(self, value):
        cap("rational_bits", max(value.numerator.bit_length(), value.denominator.bit_length()),
            self.limits["rational_bits"], "ARITHMETIC")
        return value

    def operation(self, a, b, kind):
        self.checked(a); self.checked(b)
        self.steps += 1
        cap("arithmetic_steps", self.steps, self.limits["arithmetic_steps"], "ARITHMETIC")
        # Bounded operands give at most 2B+1 temporary numerator bits.
        if kind == "add":
            value = a + b
        elif kind == "mul":
            value = a * b
        else:
            require(b != 0, "ZERO_DIVISION", "Division by zero in exact trace.")
            value = a / b
        return self.checked(value)

    def q(self, value):
        if type(value) is int:
            return self.checked(Fraction(value))
        require(type(value) is str, "RATIONAL", "An exact scalar must be an integer or rational string.")
        value = value.strip()
        parts = RATIO.fullmatch(value)
        if parts:
            numerator, denominator = map(decimal_integer, parts.groups())
        elif INTEGER.fullmatch(value):
            numerator, denominator = decimal_integer(value), 1
        else:
            parts = DECIMAL.fullmatch(value)
            if parts is None:
                unsupported("RATIONAL_ENCODING", "Unsupported exact numeric string encoding.")
            sign, whole, decimal, leading_decimal, exponent = parts.groups()
            decimal = leading_decimal if leading_decimal is not None else (decimal or "")
            numerator = decimal_integer((whole or "0") + decimal)
            if sign == "-":
                numerator = -numerator
            exponent = decimal_integer(exponent or "0")
            scale = len(decimal) - exponent
            # Bound the power before constructing it; then check its exact bits.
            cap("decimal_scale", abs(scale), 19730, "ARITHMETIC")
            power = 10 ** abs(scale)
            cap("rational_bits", power.bit_length(), self.limits["rational_bits"], "ARITHMETIC")
            cap("rational_bits", numerator.bit_length(), self.limits["rational_bits"], "ARITHMETIC")
            if scale < 0:
                numerator *= power
                denominator = 1
            else:
                denominator = power
        require(denominator != 0, "RATIONAL", "Rational denominator is zero.")
        cap("rational_bits", max(numerator.bit_length(), denominator.bit_length()),
            self.limits["rational_bits"], "ARITHMETIC")
        return self.checked(Fraction(numerator, denominator))

    def power(self, value, exponent):
        result = self.checked(Fraction(1))
        base = self.checked(value)
        while exponent:
            if exponent & 1:
                result = self.operation(result, base, "mul")
            exponent //= 2
            if exponent:
                base = self.operation(base, base, "mul")
        return result


def qtext(value):
    return integer_text(value.numerator) + "/" + integer_text(value.denominator)


def sparse(expression, variables, arithmetic):
    require(type(expression) is str, "EQUATION", "Every supplied equation must be a string.")
    cap("equation_bytes", len(expression.encode("utf-8")), MAX_AST_BYTES, "AST")
    try:
        tree = ast.parse(expression, mode="eval")
    except (SyntaxError, ValueError, RecursionError) as error:
        refuse("POLYNOMIAL_AST", "Invalid polynomial expression: " + str(error)[:160])
    cap("ast_nodes", sum(1 for _ in ast.walk(tree)), MAX_AST_NODES, "AST")
    dimension, zero = len(variables), (0,) * len(variables)
    positions = {name: index for index, name in enumerate(variables)}

    def add(a, b, sign=1):
        result = dict(a)
        for powers, coefficient in b.items():
            value = arithmetic.operation(result.get(powers, Fraction(0)), sign * coefficient, "add")
            if value:
                result[powers] = value
            else:
                result.pop(powers, None)
        cap("terms", len(result), arithmetic.limits["terms"], "AST")
        return result

    def multiply(a, b):
        cap("term_products", len(a) * len(b), arithmetic.limits["terms"], "AST")
        result = {}
        for x, cx in a.items():
            for y, cy in b.items():
                powers = tuple(i + j for i, j in zip(x, y))
                cap("power_exponent", max(powers, default=0), arithmetic.limits["power_exponent"], "AST")
                coefficient = arithmetic.operation(cx, cy, "mul")
                value = arithmetic.operation(result.get(powers, Fraction(0)), coefficient, "add")
                if value:
                    result[powers] = value
                else:
                    result.pop(powers, None)
        return result

    def visit(node, depth=0):
        cap("ast_depth", depth, MAX_JSON_DEPTH, "AST")
        if isinstance(node, ast.Constant) and type(node.value) is int:
            value = arithmetic.q(node.value)
            return {zero: value} if value else {}
        if isinstance(node, ast.Name) and node.id in positions:
            powers = list(zero); powers[positions[node.id]] = 1
            return {tuple(powers): arithmetic.checked(Fraction(1))}
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return {p: -c for p, c in visit(node.operand, depth + 1).items()}
        if isinstance(node, ast.BinOp):
            if isinstance(node.op, ast.Pow):
                require(isinstance(node.right, ast.Constant) and type(node.right.value) is int
                    and node.right.value >= 0, "POLYNOMIAL_POWER", "Power must be a nonnegative integer literal.")
                cap("ast_power", node.right.value, MAX_AST_POWER, "AST")
                cap("power_exponent", node.right.value, arithmetic.limits["power_exponent"], "AST")
                base = visit(node.left, depth + 1)
                result = {zero: arithmetic.checked(Fraction(1))}
                for _ in range(node.right.value):
                    result = multiply(result, base)
                return result
            a, b = visit(node.left, depth + 1), visit(node.right, depth + 1)
            if isinstance(node.op, ast.Add):
                return add(a, b)
            if isinstance(node.op, ast.Sub):
                return add(a, b, -1)
            if isinstance(node.op, ast.Mult):
                return multiply(a, b)
            if isinstance(node.op, ast.Div):
                require(set(b) == {zero} and b[zero] != 0, "POLYNOMIAL_DIVISION",
                    "Only division by a nonzero exact constant is supported.")
                return {p: arithmetic.operation(c, b[zero], "div") for p, c in a.items()}
        unsupported("POLYNOMIAL_AST", "Unsupported polynomial syntax, literal or variable.")

    return {"dimension": dimension, "terms": [
        {"powers": list(powers), "coefficient": qtext(coefficient)}
        for powers, coefficient in sorted(visit(tree.body).items())]}


def evaluate(row, assignment, arithmetic):
    result = arithmetic.checked(Fraction(0))
    for term in row["terms"]:
        value = arithmetic.q(term["coefficient"])
        for scalar, exponent in zip(assignment, term["powers"]):
            value = arithmetic.operation(value, arithmetic.power(scalar, exponent), "mul")
        result = arithmetic.operation(result, value, "add")
    return result


def checked_limits(supplied):
    if supplied is None:
        return dict(DEFAULT_LIMITS)
    object_fields(supplied, set(), set(HARD_LIMITS), "LIMITS")
    result = {**DEFAULT_LIMITS, **supplied}
    for key, value in result.items():
        natural(value, "LIMITS", HARD_LIMITS[key])
    return result


def checked_result(raw):
    result = parse_backend(raw)
    require(type(result) is dict and result.get("schema") == RESULT_SCHEMA, "RESULT_SCHEMA",
        "Expected the raw inherited backend RESULT.json, not a public wrapper.")
    if result.get("status") != "SAT_ONE_COHERENT_ADMITTED_SOURCE":
        unsupported("RESULT_STATUS", "Only explicit SAT_ONE_COHERENT_ADMITTED_SOURCE witness selection is supported.")
    object_fields(result, RESULT_REQUIRED, RESULT_REQUIRED, "RESULT_FIELDS")
    for key in ("unknown_size_termination_or_global_NO_claimed", "Lean_verification_claimed", "empirical_admission_claimed"):
        require(result[key] is False, "RESULT_SCOPE", "The original scope flags must explicitly be false.")
    require(result["catalogue_exhausted"] is False, "RESULT_SCOPE", "This transport is not a catalogue exclusion consumer.")
    require(result["verification"] == "INDEPENDENT_EXACT_SYMPY_WITNESS_AND_SOURCE_ADMISSION_CHECK"
        and result["scope"] == "declared complete finite registry; one graph/assignment shared across every row",
        "RESULT_VARIANT", "Unreviewed declared witness verification/scope variant.")
    require(type(result["upstream"]) is dict and type(result["software"]) is dict,
        "RESULT_METADATA", "Expected inherited source and runtime metadata objects.")
    require(type(result["elapsed_seconds"]) in (int, float) and result["elapsed_seconds"] >= 0,
        "RESULT_TIMING", "Elapsed time must be finite and nonnegative metadata.")
    require(natural(result["source_count_examined"], "RESULT_COUNT") > 0, "RESULT_COUNT", "Source count must be positive.")
    index = natural(result["witness_entry"], "ENTRY_INDEX")
    require(type(result["entries"]) is list and index < len(result["entries"]), "ENTRY_INDEX", "Explicit witness index is out of range.")
    entry = result["entries"][index]
    object_fields(entry, ENTRY_REQUIRED, ENTRY_REQUIRED, "ENTRY_FIELDS")
    require(entry["status"] == "SAT_INDEPENDENT_EXACT_WITNESS", "ENTRY_STATUS", "Selected entry is not the exact-witness variant.")
    for value, digest, code in ((result["request"], result["request_sha256"], "REQUEST_DIGEST"),
        (entry["equations"], entry["equation_sha256"], "EQUATION_DIGEST")):
        require(type(digest) is str and HEX.fullmatch(digest) and sha(canonical_bytes(value, MAX_ORIGIN_BYTES)) == digest,
            code, "Supplied inherited canonical digest does not match its payload.")
    require(type(entry["query"]) is str and type(entry["query_sha256"]) is str
        and HEX.fullmatch(entry["query_sha256"]), "QUERY_METADATA", "Expected original query filename/hash metadata.")
    return result, entry, index


def request_metadata(original, entry, arithmetic):
    object_fields(original, {"observation_kind", "n", "registry", "rows"}, REQUEST_ALLOWED, "ORIGINAL_REQUEST")
    require(original["observation_kind"] == "exact_unranked_law", "OBSERVATION_KIND", "The inherited exact-law observation tag is required.")
    if original.get("clock_contract", "free_positive_edge_specific") != "free_positive_edge_specific":
        unsupported("CLOCK_CONTRACT", "The inherited witness has a different physical clock contract.")
    require(original.get("task", "find_source") == "find_source", "ORIGINAL_TASK", "Expected a find_source result.")
    require(type(original.get("empirical_admission", {})) is dict, "EMPIRICAL_ADMISSION", "Empirical metadata must be an object.")
    if original.get("empirical_admission", {}):
        unsupported("EMPIRICAL_ADMISSION", "Measured-data admission is not a witness transport premise.")
    n = natural(original["n"], "TAXON_COUNT")
    require(n >= 2, "TAXON_COUNT", "At least two original taxa are required.")
    cap("taxa", n, 32, "NATIVE_SCOPE")
    taxa = label_list(original.get("taxa", [f"L{i}" for i in range(n)]), "TAXON_LABELS")
    require(len(taxa) == n, "TAXON_LABELS", "Taxon count differs from the public registry.")
    registry = original["registry"]
    object_fields(registry, {"complete"}, {"complete", "hybrid_ids"}, "ORIGINAL_REGISTRY")
    require(registry["complete"] is True, "ORIGINAL_REGISTRY", "The legacy registry completeness tag is missing.")
    hybrids = label_list(registry.get("hybrid_ids", []), "HYBRID_LABELS")
    modes = original.get("mechanisms", ["independent", "common"])
    require(type(modes) is list and modes and all(type(mode) is str and mode in ("common", "independent") for mode in modes)
        and len(set(modes)) == len(modes)
        and entry["mechanism"] in modes, "MECHANISM", "One declared global mechanism must match the selected entry.")
    budgets = original.get("limits", {})
    object_fields(budgets, set(), {"max_sources", "seconds", "smt_milliseconds"}, "ORIGINAL_LIMITS")
    for key in ("max_sources", "smt_milliseconds"):
        if key in budgets:
            require(natural(budgets[key], "ORIGINAL_LIMITS") > 0, "ORIGINAL_LIMITS", "Original count budgets must be positive.")
    seconds = budgets.get("seconds", 120)
    require(type(seconds) in (int, float) and 0 < seconds < 86401, "ORIGINAL_LIMITS", "Invalid original operational seconds budget.")
    rows = original["rows"]
    require(type(rows) is list and rows, "ORIGINAL_ROWS", "At least one exact observation row is required.")
    cap("observation_rows", len(rows), 4096, "NATIVE_SCOPE")
    panels = []
    for row in rows:
        object_fields(row, {"law"}, ROW_ALLOWED, "ORIGINAL_ROW")
        samples = row.get("samples", {taxon: [taxon] for taxon in taxa})
        require(type(samples) is dict and set(samples) <= set(taxa), "SAMPLE_TAXA", "Sampling addresses an unknown public taxon.")
        copies, sample_ids = [], []
        for taxon_id, taxon in enumerate(taxa):
            values = samples.get(taxon, [])
            require(type(values) is list, "SAMPLE_LABELS", "Each taxon sample must be a label list.")
            for item in values:
                copies.append(label(item, "COPY_LABELS")); sample_ids.append(taxon_id)
        require(copies and len(set(copies)) == len(copies), "COPY_LABELS", "Sample labels must be nonempty and distinct across the panel.")
        require(not ("forced" in row and "program" in row), "ROW_PROGRAM", "A row cannot have both deterministic and randomized forcing.")
        forced = row.get("forced", {})
        program = row.get("program", [{"forced": forced, "weight": "1"}])
        require(type(program) is list and program, "ROW_PROGRAM", "Program support must be nonempty.")
        total = arithmetic.checked(Fraction(0))
        any_forcing = False
        for operation in program:
            object_fields(operation, set(), {"forced", "weight"}, "ROW_PROGRAM")
            mask = operation.get("forced", {})
            require(type(mask) is dict and set(mask) <= set(hybrids)
                and all(type(bit) is int and bit in (0, 1) for bit in mask.values()),
                "FORCED_PARENT", "Forcing must retain original hybrid IDs and incoming occurrence bits.")
            any_forcing |= bool(mask)
            weight = arithmetic.q(operation.get("weight", "1"))
            require(0 < weight <= 1, "PROGRAM_WEIGHT", "Program weights must be exact and strictly positive.")
            total = arithmetic.operation(total, weight, "add")
        require(total == 1, "PROGRAM_WEIGHT", "Program weights must sum exactly to one.")
        kind = row.get("readout", "rooted")
        if kind not in ("rooted", "unrooted_splits", "joint_quartets"):
            unsupported("READOUT", "The inherited row uses a different observer.")
        law = row["law"]
        require(type(law) is list and law, "OBSERVATION_LAW", "A complete supplied exact probability list is required.")
        mass = arithmetic.checked(Fraction(0))
        for event in law:
            object_fields(event, {"outcome", "p"}, {"outcome", "p"}, "OBSERVATION_LAW")
            probability = arithmetic.q(event["p"])
            require(0 <= probability <= 1, "OBSERVATION_LAW", "A supplied probability is outside [0,1].")
            mass = arithmetic.operation(mass, probability, "add")
        require(mass == 1, "OBSERVATION_LAW", "Supplied row probabilities must sum to one.")
        panels.append((copies, sample_ids, kind, any_forcing, "program" in row))
    return taxa, hybrids, panels


def carrier(entry, taxa, hybrid_labels):
    graph = entry["graph"]
    object_fields(graph, {"edges", "root", "leaves"}, {"edges", "root", "leaves"}, "GRAPH")
    edges = graph["edges"]
    require(type(edges) is list and len(edges) >= 2, "GRAPH_EDGES", "Expected original ordered edge occurrences.")
    cap("original_edges", len(edges) + 1, 32, "NATIVE_SCOPE")
    names, by_name = [], {}
    for edge in edges:
        require(type(edge) is list and len(edge) == 2, "GRAPH_EDGE", "An original edge is an ordered endpoint pair.")
        for vertex in edge:
            label(vertex, "VERTEX_NAMES")
            if vertex not in by_name:
                by_name[vertex] = len(names); names.append(vertex)
    cap("vertices", len(names), 32, "NATIVE_SCOPE")
    label(graph["root"], "GRAPH_ROOT")
    require(graph["root"] in by_name, "GRAPH_ROOT", "Root is absent from the original edge registry.")
    leaves = label_list(graph["leaves"], "GRAPH_LEAVES")
    internal_leaves = [f"L{i}" for i in range(len(taxa))]
    require(set(leaves) == set(internal_leaves) and all(v in by_name for v in internal_leaves),
        "TAXON_VERTEX_MAP", "The old L_i alphabet must match the public taxa[i] bijection.")
    incoming = {v: [i for i, edge in enumerate(edges) if edge[1] == v] for v in names}
    hybrids = sorted(v for v in names if len(incoming[v]) == 2)
    require(set(hybrids) == {f"H{i}" for i in range(len(hybrid_labels))}, "HYBRID_VERTEX_MAP",
        "Internal H_i names must match the declared original hybrid registry.")
    cap("source_bank", len(names) + len(edges) + 1 + len(hybrids), 32, "NATIVE_SCOPE")
    variables = [f"x{i}" for i in range(len(edges))] + [f"g_{v}" for v in hybrids]
    return names, by_name, hybrids, incoming, variables


def checked_physical(entry, names, variables):
    physical = entry["physical_realization"]
    fields = {"original_vertex_ages", "contemporaneous_tip_age", "original_edges",
        "ancestral_root_rate", "natural_inheritance_values", "clock_scope"}
    object_fields(physical, fields, fields, "PHYSICAL_FIELDS")
    ages, graph = physical["original_vertex_ages"], entry["graph"]
    require(type(ages) is dict and set(ages) == set(names), "PHYSICAL_AGES", "Physical ages must bind every original vertex exactly once.")
    for vertex in names:
        natural(ages[vertex], "PHYSICAL_AGES")
        children = [child for parent, child in graph["edges"] if parent == vertex]
        if vertex in graph["leaves"]:
            require(not children and ages[vertex] == 0, "PHYSICAL_AGES", "Original tips must have the saved height-calendar age zero.")
        else:
            require(children and ages[vertex] == 1 + max(ages[child] for child in children),
                "PHYSICAL_AGES", "Saved ages differ from the inherited integer height construction.")
    require(type(physical["contemporaneous_tip_age"]) is int and physical["contemporaneous_tip_age"] == 0
        and physical["ancestral_root_rate"] == "1", "PHYSICAL_CONVENTION", "Tip/ancestral conventions differ from the inherited witness.")
    require(type(physical["original_edges"]) is list and len(physical["original_edges"]) == len(graph["edges"]),
        "PHYSICAL_EDGES", "Physical edge records must preserve every original occurrence.")
    for index, (parent, child) in enumerate(graph["edges"]):
        record = physical["original_edges"][index]
        required = {"original_edge_id", "parent", "child", "duration", "survival_parameter",
            "survival_value", "positive_rate_definition"}
        object_fields(record, required, required, "PHYSICAL_EDGE")
        duration = ages[parent] - ages[child]
        require(type(record["original_edge_id"]) is int and record["original_edge_id"] == index
            and record["parent"] == parent and record["child"] == child
            and type(record["duration"]) is int and record["duration"] == duration and duration > 0
            and record["survival_parameter"] == f"x{index}"
            and record["survival_value"] == entry["values"][f"x{index}"]
            and record["positive_rate_definition"] == "-log(survival_value)/duration",
            "PHYSICAL_EDGE", "Original occurrence, survival or logarithmic rate metadata changed.")
    require(physical["natural_inheritance_values"] == {v: entry["values"][v] for v in variables if v.startswith("g_")},
        "PHYSICAL_GAMMA", "Inheritance metadata must use the same old parent-zero gamma bank.")
    require(physical["clock_scope"] == "free positive edge-specific rates; exact real logarithmic definitions, not decimal approximations",
        "PHYSICAL_CONVENTION", "Unreviewed physical clock scope.")


def export_witness(raw_backend_result, panel_row_index, global_labels=None, limits=None):
    """Return (unchanged native DTO, separate origin). Execute no target code.

    Rational assignments are checked on the entire supplied trace. Algebraic
    descriptors are retained exactly; their positivity/equation evaluation is
    unsupported here and by the current native bank. Only explicit top-level
    SAT_ONE/witness_entry selection is accepted. The panel index never selects
    or removes equations, observations, randomization actions or fit variables.
    """
    limits = checked_limits(limits)
    arithmetic = Arithmetic(limits)
    result, entry, index = checked_result(raw_backend_result)
    taxa, public_hybrids, panels = request_metadata(result["request"], entry, arithmetic)
    panel_row_index = natural(panel_row_index, "PANEL_INDEX")
    require(panel_row_index < len(panels), "PANEL_INDEX", "Selected panel row is out of range.")
    copies, samples, reader, forced, randomized = panels[panel_row_index]
    cap("selected_copies", len(copies), 4, "NATIVE_SCOPE")
    if global_labels is None:
        global_labels = list(range(len(copies)))
    require(type(global_labels) is list and len(global_labels) == len(copies), "GLOBAL_LABELS", "Provide one global ID for every selected copy.")
    global_labels = [natural(v, "GLOBAL_LABELS") for v in global_labels]
    require(len(set(global_labels)) == len(global_labels), "GLOBAL_LABELS", "Global label embedding must be injective.")
    names, by_name, hybrids, incoming, variables = carrier(entry, taxa, public_hybrids)
    require(type(entry["values"]) is dict and set(entry["values"]) == set(variables), "VALUE_BANK", "Witness keys do not match the original E/old-g bank.")
    values, assignment, algebraic = [], [], []
    for variable in variables:
        value = entry["values"][variable]
        require(type(value) is dict, "VALUE_ENCODING", "Expected an exact value descriptor.")
        if value.get("kind") == "rational":
            object_fields(value, {"kind", "value"}, {"kind", "value"}, "VALUE_ENCODING")
            scalar = arithmetic.q(value["value"])
            require(0 < scalar < 1, "STRICT_INTERIOR", "All supplied survival/gamma rationals must be strictly interior.")
            values.append({"kind": "RATIONAL", "value": qtext(scalar)}); assignment.append(scalar)
        elif value.get("kind") == "algebraic":
            fields = {"kind", "polynomial_ascending", "real_root_index"}
            object_fields(value, fields, fields, "VALUE_ENCODING")
            polynomial = value["polynomial_ascending"]
            require(type(polynomial) is list and 2 <= len(polynomial) <= 65, "ALGEBRAIC_DESCRIPTOR", "Algebraic polynomial degree is outside the native descriptor scope.")
            coefficients = [arithmetic.q(c) for c in polynomial]
            root = natural(value["real_root_index"], "ALGEBRAIC_DESCRIPTOR")
            require(coefficients[-1] != 0 and 1 <= root < len(coefficients), "ALGEBRAIC_DESCRIPTOR", "Keep a nonzero leading coefficient and the old one-based root index.")
            values.append({"kind": "ALGEBRAIC", "polynomial_ascending": [qtext(c) for c in coefficients], "real_root_index": root})
            assignment.append(None); algebraic.append(variable)
        else:
            unsupported("VALUE_ENCODING", "The supplied exact value codec is not supported.")
    checked_physical(entry, names, variables)
    expressions = entry["equations"]
    require(type(expressions) is list and expressions, "TRACE", "The full supplied coupled trace must be nonempty.")
    cap("equations", len(expressions), limits["equations"], "TRACE")
    equations, total_terms = [], 0
    for expression in expressions:
        row = sparse(expression, variables, arithmetic)
        total_terms += len(row["terms"])
        cap("terms", total_terms, limits["terms"], "TRACE")
        equations.append(row)
    if not algebraic:
        for index_in_trace, row in enumerate(equations):
            require(evaluate(row, assignment, arithmetic) == 0, "TRACE_NOT_SATISFIED",
                "Shared rational assignment fails supplied equation " + str(index_in_trace) + ".")
    request = {"schema": "source_fit_request_v1",
        "context": {"vertices": len(names), "root": by_name[entry["graph"]["root"]],
            "edges": [[by_name[p], by_name[c]] for p, c in entry["graph"]["edges"]],
            "leaves": [by_name[f"L{i}"] for i in range(len(taxa))],
            "hybrids": [[by_name[h], *incoming[h]] for h in hybrids],
            "local_samples": samples, "global_labels": global_labels},
        "vertex_names": names, "taxon_labels": taxa,
        "hybrid_labels": [public_hybrids[int(h[1:])] for h in hybrids],
        "copy_labels": copies, "variables": variables, "values": values,
        "equations": equations, "mechanism": entry["mechanism"].upper(),
        "terminal": "ANCESTRAL_COMPLETE", "compiler_limits": dict(COMPILER_LIMITS), "limits": limits}
    request_bytes = canonical_bytes(request, MAX_REQUEST_BYTES, newline=True)
    origin = {"schema": "source_fit_witness_transport_v1", "status": "EXPORTED",
        "raw_backend_sha256": sha(raw_backend_result), "raw_backend_bytes": len(raw_backend_result),
        "native_request_sha256": sha(request_bytes), "native_request_bytes": len(request_bytes),
        "selected_entry_index": index, "selected_panel_row_index": panel_row_index,
        "original_request_sha256": result["request_sha256"], "original_equation_sha256": entry["equation_sha256"],
        "original_request": result["request"], "selected_entry": entry,
        "selected_row": result["request"]["rows"][panel_row_index],
        "all_original_rows_retained": True, "all_supplied_equations_retained": True,
        "original_observation_rows": len(panels), "supplied_equations": len(equations), "supplied_terms": total_terms,
        "original_request_digest_checked": True, "original_equation_digest_checked": True,
        "supplied_trace_arithmetic_checked": not algebraic,
        "native_evaluation_supported": not algebraic,
        "native_evaluation_scope": "RATIONAL_BANK" if not algebraic else "UNSUPPORTED_ALGEBRAIC_EVALUATION",
        "unsupported_algebraic_variables": algebraic,
        "requested_observer": "NATURAL_ROOTED_UNRANKED_COMPLETE",
        "selected_row_reader": reader,
        "selected_row_relation": "COUNTERFACTUAL_NATURAL_ROOTED_OBSERVER" if reader != "rooted" or forced or randomized
            else "NATURAL_ROOTED_OBSERVER_REQUESTED_NOT_REVERIFIED",
        "selected_row_actions_retained": True,
        "vertex_bijection": [{"native_vertex": i, "internal_vertex": v} for i, v in enumerate(names)],
        "taxon_bijection": [{"taxon_id": i, "public_taxon": t, "internal_vertex": f"L{i}", "native_vertex": by_name[f"L{i}"]}
            for i, t in enumerate(taxa)],
        "copy_bijection": [{"local_copy": i, "original_copy_label": c, "taxon_id": samples[i], "global_id": global_labels[i]}
            for i, c in enumerate(copies)],
        "hybrid_bijection": [{"native_hybrid": i, "internal_vertex": h,
            "original_hybrid_label": public_hybrids[int(h[1:])], "incoming_occurrences": incoming[h],
            "old_gamma_variable": "g_" + h, "old_gamma_parent": 0, "native_gamma_conversion": "1-old_gamma"}
            for i, h in enumerate(hybrids)],
        "original_edge_order": [dict(record) for record in entry["physical_realization"]["original_edges"]],
        "legacy_declared_verification": result["verification"], "legacy_declared_scope": result["scope"],
        "legacy_upstream_metadata": result["upstream"], "legacy_software_metadata": result["software"],
        "transport_work": {"arithmetic_steps": arithmetic.steps}, "contract_pins": dict(CONTRACT_PINS),
        "fitter_called": False, "semantic_source_checker_called": False, "native_solver_called": False,
        **{key: False for key in SCIENCE_FALSE}}
    canonical_bytes(origin, MAX_SIDECAR_BYTES, newline=True)
    return request, origin


def write_new(path, raw):
    with path.open("xb") as handle:
        handle.write(raw)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fit-result", type=Path, required=True)
    parser.add_argument("--row-index", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    # An existing output is never altered, including failed prior attempts.
    try:
        args.output.mkdir(parents=True, exist_ok=False)
    except OSError as error:
        print(json.dumps({"schema": "source_fit_witness_transport_cli_v1", "status": "EXECUTION_FAILURE",
            "code": "OUTPUT_NOT_NEW", "detail": str(error)[:256]}), file=sys.stderr)
        return 1
    receipt = {"schema": "source_fit_witness_transport_cli_v1", "fit_result_path": str(args.fit_result),
        "output_path": str(args.output), "selected_panel_row_index": args.row_index,
        "fitter_called": False, "semantic_source_checker_called": False, "native_solver_called": False,
        **{key: False for key in SCIENCE_FALSE}}
    exit_code = 0
    try:
        with args.fit_result.open("rb") as handle:
            raw = handle.read(MAX_ORIGIN_BYTES + 1)
        cap("origin_bytes", len(raw), MAX_ORIGIN_BYTES, "INPUT")
        write_new(args.output / "BACKEND-RESULT.json", raw)
        receipt.update(raw_backend_sha256=sha(raw), raw_backend_bytes=len(raw))
        request, origin = export_witness(raw, args.row_index)
        request_raw = canonical_bytes(request, MAX_REQUEST_BYTES, newline=True)
        origin_raw = canonical_bytes(origin, MAX_SIDECAR_BYTES, newline=True)
        write_new(args.output / "SOURCE-FIT-REQUEST.json", request_raw)
        write_new(args.output / "ORIGIN.json", origin_raw)
        receipt.update(status="EXPORTED", native_request_sha256=sha(request_raw),
            origin_sha256=sha(origin_raw), native_evaluation_supported=origin["native_evaluation_supported"],
            native_evaluation_scope=origin["native_evaluation_scope"],
            supplied_trace_arithmetic_checked=origin["supplied_trace_arithmetic_checked"],
            selected_row_relation=origin["selected_row_relation"])
    except TransportError as error:
        receipt.update(status=error.status, code=error.code, detail=error.detail)
        if error.limit is not None:
            receipt["limit"] = error.limit
        exit_code = 2 if error.status in ("UNSUPPORTED", "UNKNOWN") else 1
    except (OSError, UnicodeError, RecursionError, ValueError, TypeError, KeyError, IndexError) as error:
        receipt.update(status="EXECUTION_FAILURE", code="TRANSPORT_EXECUTION_FAILURE", detail=str(error)[:256])
        exit_code = 1
    receipt["exit_code"] = exit_code
    try:
        write_new(args.output / "RESULT.json", canonical_bytes(receipt, MAX_REQUEST_BYTES, newline=True))
    except (OSError, TransportError) as error:
        print(json.dumps({"schema": "source_fit_witness_transport_cli_v1", "status": "EXECUTION_FAILURE",
            "code": "RECEIPT_WRITE_FAILURE", "detail": str(error)[:256]}), file=sys.stderr)
        return 1
    print(canonical_bytes(receipt, MAX_REQUEST_BYTES).decode("ascii"))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())
