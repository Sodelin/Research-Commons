#!/usr/bin/env python3
"""Exact natural rooted-law reference using the attributed Oct 1 compiler.

This consumer compares every whole-edge polynomial coefficient and rational
probability. It does not reconstruct an observation trace or certify a source,
timed law, native implementation, or resource exhaustion. The native bank and
work metadata require their separately reported checks. No Rust code is called.

The isolated adapter can call install_baseline(captured_bytes) before this
module's verifier. Otherwise the standalone CLI authenticates the same file.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys
from types import ModuleType

from certificate_check import MAX_REQUEST_BYTES, MAX_CERTIFICATE_BYTES, require, qtext, read_bounded
from chart_check import Chart, structural_checks

BASELINE_SHA = "eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7"
BASELINE_ALIAS = "source_fit_pinned_oct1_law_compiler"
BASELINE_PATH = Path(__file__).resolve().parents[2] / "2026-10-01-g7-continuous-design/law_compiler.py"
MAX_NAT = (1 << 64) - 1
HARD_RATIONAL_BITS = 65536
BACKEND_REQUIREMENTS = {"sympy": "1.14.0", "mpmath": "1.3.0"}
Q_TOKEN = re.compile(r"(?:0|[1-9][0-9]*|-[1-9][0-9]*)/[1-9][0-9]*\Z")
N_TOKEN = re.compile(r"(?:0|[1-9][0-9]*)\Z")
FALSE_GATES = (
    "source_admission_verified", "source_observation_fit_verified", "source_provenance_verified",
    "timed_readout_verified", "certificate_valid", "full_solver_verified",
)
ROOTED_FALSE_GATES = FALSE_GATES + ("full_code_evaluated", "universal_native_refinement_verified")
REQUEST_KEYS = {
    "schema", "context", "vertex_names", "taxon_labels", "hybrid_labels", "copy_labels",
    "variables", "values", "equations", "mechanism", "terminal", "compiler_limits", "limits",
}
CONTEXT_KEYS = {"vertices", "root", "edges", "leaves", "hybrids", "local_samples", "global_labels"}
LIMIT_MAXIMA = {"equations": 4096, "terms": 65536, "arithmetic_steps": 1000000,
                "rational_bits": 65536, "power_exponent": 4096}
COMPILER_MAXIMA = {"word_length": 32, "slots": 16, "variables": 256}


def keys(value, expected, where):
    require(type(value) is dict and set(value) == set(expected), f"{where}: wrong object fields")


def nat(value, where, maximum=MAX_NAT):
    require(type(value) is int and 0 <= value <= maximum, f"{where}: expected bounded natural")
    return value


def strict_equal(left, right):
    """JSON Boolean/integer and object/list distinctions are part of binding."""
    if type(left) is not type(right):
        return False
    if type(left) is dict:
        return set(left) == set(right) and all(strict_equal(left[k], right[k]) for k in left)
    if type(left) is list:
        return len(left) == len(right) and all(strict_equal(a, b) for a, b in zip(left, right))
    return left == right


def _pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, "duplicate JSON object key")
        result[key] = value
    return result


def _integer(token):
    # All integer fields in these two schemas are nonnegative u64 values.
    require(token == "-0" or (len(token) <= 20 and bool(N_TOKEN.fullmatch(token))),
            "JSON integer is not a bounded natural")
    return nat(int(token), "JSON integer")


def _not_integer(token):
    raise ValueError("floating/exponent/nonfinite JSON number is forbidden")


def json_frame(raw, byte_cap):
    require(type(raw) is bytes and 0 < len(raw) <= byte_cap, "JSON byte frame exceeds cap")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=_pairs, parse_int=_integer,
                      parse_float=_not_integer, parse_constant=_not_integer)


def rational(token, bits=HARD_RATIONAL_BITS):
    require(type(token) is str and bool(Q_TOKEN.fullmatch(token)), "noncanonical rational token")
    numerator, denominator = map(int, token.split("/"))
    require(max(abs(numerator).bit_length(), denominator.bit_length()) <= bits,
            "rational bit cap before normalization")
    value = Fraction(numerator, denominator)
    require(qtext(value) == token, "unreduced rational token")
    return value


def _labels(values, size, where):
    require(type(values) is list and len(values) == size, f"{where}: wrong label count")
    require(all(type(v) is str and 1 <= len(v.encode("utf-8")) <= 128 and "\0" not in v
                for v in values), f"{where}: invalid UTF-8 label")
    require(len(set(values)) == size, f"{where}: repeated label")


def _limits(value, maxima, where):
    keys(value, maxima, where)
    for key, maximum in maxima.items():
        nat(value[key], f"{where}.{key}", maximum)


def parse_request(raw):
    """Validate the bounded semantic DTO; no equation or law is evaluated."""
    request = json_frame(raw, MAX_REQUEST_BYTES)
    keys(request, REQUEST_KEYS, "request")
    require(request["schema"] == "source_fit_request_v1", "wrong source-fit request schema")
    context = request["context"]
    keys(context, CONTEXT_KEYS, "context")
    v = nat(context["vertices"], "vertices", 32)
    require(v >= 3, "source needs at least three vertices")
    root = nat(context["root"], "root", v - 1)
    edges, leaves, hybrids = context["edges"], context["leaves"], context["hybrids"]
    require(type(edges) is list and 2 <= len(edges) <= 31, "original edge count outside bank cap")
    require(type(leaves) is list and 2 <= len(leaves) <= v, "wrong original leaf count")
    require(type(hybrids) is list and len(hybrids) <= v, "wrong original hybrid count")
    require(v + len(edges) + 1 + len(hybrids) <= 32, "source bank dimension exceeds cap")
    for edge in edges:
        require(type(edge) is list and len(edge) == 2, "wrong edge occurrence arity")
        for endpoint in edge:
            nat(endpoint, "edge endpoint", v - 1)
    for leaf in leaves:
        nat(leaf, "leaf", v - 1)
    for hybrid in hybrids:
        require(type(hybrid) is list and len(hybrid) == 3, "wrong hybrid registry arity")
        nat(hybrid[0], "hybrid vertex", v - 1)
        nat(hybrid[1], "incoming0", len(edges) - 1)
        nat(hybrid[2], "incoming1", len(edges) - 1)
        require(hybrid[1] < hybrid[2], "incoming occurrences must retain inherited input order")
    samples, labels = context["local_samples"], context["global_labels"]
    require(type(samples) is list and type(labels) is list and len(samples) == len(labels) <= 4,
            "selected panel must contain at most four copies")
    for sample in samples:
        nat(sample, "sample taxon", len(leaves) - 1)
    for label in labels:
        nat(label, "global copied label")
    require(len(set(labels)) == len(labels), "global label embedding is not injective")
    structural_checks(Chart(v, root, tuple(map(tuple, edges)), tuple(leaves), tuple(map(tuple, hybrids)),
                            (), (), tuple((None, None) for _ in hybrids), 4096))
    for key, size in (("vertex_names", v), ("taxon_labels", len(leaves)),
                      ("hybrid_labels", len(hybrids)), ("copy_labels", len(samples))):
        _labels(request[key], size, key)
    names = request["vertex_names"]
    require(all(names[a[0]] < names[b[0]] for a, b in zip(hybrids, hybrids[1:])),
            "hybrid IDs differ from inherited sorted-name order")
    dimension = len(edges) + len(hybrids)
    expected = [f"x{i}" for i in range(len(edges))] + ["g_" + names[h[0]] for h in hybrids]
    require(strict_equal(request["variables"], expected), "wrong original variable bank")
    require(request["mechanism"] in ("COMMON", "INDEPENDENT"), "wrong inheritance mechanism")
    require(request["terminal"] in ("FULL_VIEW", "ANCESTRAL_COMPLETE"), "wrong terminal readout")
    require(request["terminal"] != "ANCESTRAL_COMPLETE" or samples, "empty completion panel")
    _limits(request["limits"], LIMIT_MAXIMA, "limits")
    _limits(request["compiler_limits"], COMPILER_MAXIMA, "compiler_limits")
    values = request["values"]
    require(type(values) is list and len(values) == dimension, "wrong assignment dimension")
    for value in values:
        require(type(value) is dict, "wrong exact-value object")
        if value.get("kind") == "RATIONAL":
            keys(value, {"kind", "value"}, "rational assignment")
            require(0 < rational(value["value"]) < 1, "assignment is not strictly interior")
        else:
            keys(value, {"kind", "polynomial_ascending", "real_root_index"}, "algebraic descriptor")
            require(value["kind"] == "ALGEBRAIC", "wrong exact-value kind")
            coefficients = value["polynomial_ascending"]
            require(type(coefficients) is list and 2 <= len(coefficients) <= 65,
                    "wrong algebraic descriptor degree")
            qs = [rational(q) for q in coefficients]
            index = nat(value["real_root_index"], "algebraic root index", len(qs) - 1)
            require(index > 0 and qs[-1] != 0, "invalid algebraic root descriptor")
    equations = request["equations"]
    require(type(equations) is list and 1 <= len(equations) <= 4096, "wrong supplied equation count")
    count = 0
    for equation in equations:
        keys(equation, {"dimension", "terms"}, "supplied equation")
        require(nat(equation["dimension"], "equation dimension") == dimension, "equation bank mismatch")
        terms = equation["terms"]
        require(type(terms) is list, "wrong supplied term list")
        count += len(terms)
        require(count <= 65536, "supplied term count exceeds hard cap")
        previous = None
        for term in terms:
            keys(term, {"powers", "coefficient"}, "supplied term")
            powers = term["powers"]
            require(type(powers) is list and len(powers) == dimension, "wrong term dimension")
            for power in powers:
                nat(power, "supplied exponent", 4096)
            require(previous is None or previous < powers, "terms not unique canonical lex order")
            previous = powers
            require(rational(term["coefficient"]) != 0, "zero sparse term")
    return request


def bank_request(request):
    """The native bank echo uses pairs/lowercase kinds, not the input DTO."""
    result = dict(request)
    result["schema"] = "source_fit_bank_request_v1"
    result["values"] = [dict(value, kind=value["kind"].lower()) for value in request["values"]]
    result["equations"] = [{"dimension": e["dimension"], "terms": [[t["powers"], t["coefficient"]]
                           for t in e["terms"]]} for e in request["equations"]]
    return result


def default_readout_request(hybrids):
    return {
        "observer": "ROOTED_UNRANKED_COMPLETE", "forget_configuration_label": True,
        "program": [{"label": "natural", "weight": "1/1", "forcing": [None] * hybrids}],
        "word_limits": {"initial_assignments": 16, "initial_terms": 256, "queries": 4096,
                        "branches": 65536, "term_products": 262144, "destinations": 4096, "terms": 65536},
        "provider_limits": {
            "epoch": {"calls": 4096, "destinations": 4096, "lifted_terms": 65536,
                      "branches": 4096, "term_products": 65536},
            "boundary": {"assignments": 16, "destinations": 16, "term_contributions": 128},
            "completion": {"calls": 4096, "destinations": 4096, "lifted_terms": 65536}},
        "limits": {"word_rows": 4096, "monomial_contributions": 262144, "normalized_terms": 65536,
                   "arithmetic_steps": 1000000, "rational_bits": 4096, "power_exponent": 4096},
    }


def _bits(q):
    return max(abs(q.numerator).bit_length(), q.denominator.bit_length())


class ExactArithmetic:
    """Bit bounds prevent hostile powers; this does not mirror native work."""
    def __init__(self, bits=HARD_RATIONAL_BITS):
        self.bits = bits

    def check(self, value):
        require(_bits(value) <= self.bits, "reference arithmetic bit bound exceeded")
        return value

    def add(self, left, right):
        self.check(left); self.check(right)
        return self.check(left + right)

    def multiply(self, left, right):
        self.check(left); self.check(right)
        return self.check(left * right)

    def power(self, base, exponent):
        nat(exponent, "reference exponent", 4096)
        self.check(base)
        result = self.check(Fraction(1))
        while exponent:
            if exponent & 1:
                result = self.multiply(result, base)
            exponent >>= 1
            if exponent:
                base = self.multiply(base, base)
        return result


def evaluate(polynomial, values, arithmetic):
    result = Fraction(0)
    for powers, coefficient in polynomial.items():
        require(len(powers) == len(values), "evaluation dimension mismatch")
        term = arithmetic.check(coefficient)
        for value, power in zip(values, powers):
            if power:
                term = arithmetic.multiply(term, arithmetic.power(value, power))
        result = arithmetic.add(result, term)
    return result


def check_supplied_trace(request):
    require(all(value["kind"] == "RATIONAL" for value in request["values"]),
            "independent algebraic evaluation is unsupported")
    values = [rational(value["value"]) for value in request["values"]]
    arithmetic = ExactArithmetic(request["limits"]["rational_bits"])
    for value in values:
        arithmetic.check(value)
    require(len(request["equations"]) <= request["limits"]["equations"], "TABLE exceeds equation limit")
    require(sum(len(e["terms"]) for e in request["equations"]) <= request["limits"]["terms"],
            "TABLE exceeds term limit")
    for equation in request["equations"]:
        polynomial = {tuple(t["powers"]): rational(t["coefficient"]) for t in equation["terms"]}
        require(all(max(powers, default=0) <= request["limits"]["power_exponent"] for powers in polynomial),
                "TABLE exceeds declared exponent limit")
        require(evaluate(polynomial, values, arithmetic) == 0, "supplied trace does not vanish at shared assignment")
    return values


def install_baseline(raw):
    """Authenticate captured provider bytes before executing them in the child."""
    require(type(raw) is bytes and hashlib.sha256(raw).hexdigest() == BASELINE_SHA,
            "inherited compiler source pin mismatch")
    module = ModuleType(BASELINE_ALIAS)
    module.__file__ = "<pinned-Oct1-law_compiler.py>"
    sys.modules[BASELINE_ALIAS] = module  # dataclass resolves this exact module
    try:
        exec(compile(raw, module.__file__, "exec"), module.__dict__)
        module.__source_fit_source_sha256__ = BASELINE_SHA
    except BaseException:
        sys.modules.pop(BASELINE_ALIAS, None)
        raise
    return module


def baseline_module():
    module = sys.modules.get(BASELINE_ALIAS)
    if module is None:
        module = install_baseline(BASELINE_PATH.read_bytes())
    require(getattr(module, "__source_fit_source_sha256__", None) == BASELINE_SHA,
            "unverified inherited compiler module")
    import sympy
    import mpmath
    require(sympy.__version__ == BACKEND_REQUIREMENTS["sympy"]
            and mpmath.__version__ == BACKEND_REQUIREMENTS["mpmath"], "reference backend version mismatch")
    return module


def leaves(tree):
    return (tree,) if type(tree) is int else leaves(tree[0]) + leaves(tree[1])


def tree_wire(tree):
    return str(tree) if type(tree) is int else "(" + tree_wire(tree[0]) + "," + tree_wire(tree[1]) + ")"


def _mapped_tree(tree, embedding):
    if type(tree) is str:
        require(tree in embedding, "inherited tree has unknown copied label")
        return embedding[tree]
    require(type(tree) is tuple and len(tree) == 2, "inherited tree is not binary")
    left, right = (_mapped_tree(child, embedding) for child in tree)
    return (left, right) if min(leaves(left)) < min(leaves(right)) else (right, left)


def parse_tree(token, expected_labels):
    require(type(token) is str and 1 <= len(token) <= 128, "rooted tree frame exceeds four-copy grammar")

    def read(index):
        require(index < len(token), "truncated rooted tree")
        if token[index] == "(":
            left, index = read(index + 1)
            require(index < len(token) and token[index] == ",", "missing tree separator")
            right, index = read(index + 1)
            require(index < len(token) and token[index] == ")", "missing tree close")
            require(min(leaves(left)) < min(leaves(right)), "tree child order is not canonical")
            return (left, right), index + 1
        end = index
        while end < len(token) and "0" <= token[end] <= "9":
            end += 1
        number = token[index:end]
        require(len(number) <= 20 and bool(N_TOKEN.fullmatch(number)), "invalid tree leaf")
        return nat(int(number), "tree global label"), end

    tree, end = read(0)
    require(end == len(token) and sorted(leaves(tree)) == sorted(expected_labels),
            "tree omits or repeats a global copied label")
    require(tree_wire(tree) == token, "noncanonical tree serialization")
    return tree


def reference_polynomials(request):
    """Call the pinned full-joint compiler; no caller string reaches sympify."""
    import sympy as sp
    baseline = baseline_module()
    context = request["context"]
    hybrids = {h[0]: hid for hid, h in enumerate(context["hybrids"])}
    vertex = lambda v: f"H{hybrids[v]:04d}" if v in hybrids else f"V{v:04d}"
    network = baseline.Network(tuple((vertex(a), vertex(b)) for a, b in context["edges"]),
                               vertex(context["root"]), tuple(vertex(v) for v in context["leaves"]))
    incoming, _, _, provider_hybrids = network.structure()
    require(provider_hybrids == tuple(vertex(h[0]) for h in context["hybrids"]), "safe hybrid ordering changed")
    for h in context["hybrids"]:
        require(incoming[vertex(h[0])] == h[1:], "inherited incoming occurrence ordering changed")
    symbols = tuple(sp.Symbol(f"x{i}") for i in range(len(context["edges"])))
    values = [rational(value["value"], 4096) for value in request["values"]]
    gammas = {vertex(h[0]): sp.Rational(values[len(symbols) + hid].numerator,
                                      values[len(symbols) + hid].denominator)
              for hid, h in enumerate(context["hybrids"])}
    samples, embedding = {}, {}
    for copied, taxon in enumerate(context["local_samples"]):
        name = f"C{copied:04d}"
        leaf = vertex(context["leaves"][taxon])
        samples[leaf] = (*samples.get(leaf, ()), name)
        embedding[name] = context["global_labels"][copied]
    law = baseline.compile_law(network, request["mechanism"].lower(), samples=samples,
                               edge_values=dict(enumerate(symbols)), inheritance_values=gammas)
    output = {}
    for tree, expression in law.items():
        name = tree_wire(_mapped_tree(tree, embedding))
        parse_tree(name, context["global_labels"])
        polynomial = output.setdefault(name, {})
        for powers, coefficient in sp.Poly(sp.expand(expression), *symbols, domain=sp.QQ).terms():
            powers = tuple(map(int, powers))
            require(all(0 <= power <= 4096 for power in powers), "reference polynomial exponent exceeds cap")
            value = Fraction(int(coefficient.p), int(coefficient.q))
            ExactArithmetic().check(value)
            polynomial[powers] = ExactArithmetic().add(polynomial.get(powers, Fraction(0)), value)
            if polynomial[powers] == 0:
                del polynomial[powers]
    return {name: polynomial for name, polynomial in output.items() if polynomial}


def _false_flags(response, names):
    for name in names:
        require(response.get(name) is False, f"unestablished gate {name} was promoted")


def _limit(limit):
    require(type(limit) is dict and {"stage", "kind", "required", "cap"} <= set(limit)
            and set(limit) <= {"stage", "kind", "required", "cap", "population"}, "wrong UNKNOWN limit fields")
    require(type(limit["stage"]) is str and type(limit["kind"]) is str
            and 1 <= len(limit["stage"]) <= 128 and 1 <= len(limit["kind"]) <= 128, "wrong UNKNOWN stage/kind")
    nat(limit["cap"], "UNKNOWN cap")
    required = limit["required"]
    if type(required) is str:
        require(len(required) <= 20 and bool(N_TOKEN.fullmatch(required)), "wrong UNKNOWN required count")
        required = nat(int(required), "UNKNOWN required")
    else:
        required = nat(required, "UNKNOWN required")
    require(required > limit["cap"], "UNKNOWN count does not exceed claimed cap")
    if "population" in limit and limit["population"] is not None:
        population = limit["population"]
        require(type(population) is list and len(population) == 2 and population[0] in ("V", "E", "A"),
                "wrong UNKNOWN population tag")
        nat(population[1], "UNKNOWN population ID")


def check_bank_frame(request, response):
    require(type(response) is dict and response.get("schema") == "source_fit_bank_result_v1", "wrong bank result schema")
    _false_flags(response, FALSE_GATES)
    require(strict_equal(response.get("request"), bank_request(request)), "semantic request echo changed")
    base = {"schema", "status", "request", "supplied_trace_checked", *FALSE_GATES}
    status = response.get("status")
    if status == "SYMBOLIC_BANK":
        keys(response, base | {"bank"}, "symbolic bank response")
        require(response["supplied_trace_checked"] is True and type(response["bank"]) is dict, "wrong successful bank frame")
    elif status == "UNKNOWN":
        keys(response, base | {"limit"}, "bank UNKNOWN")
        require(response["supplied_trace_checked"] is False, "UNKNOWN promoted trace check")
        _limit(response["limit"])
    else:
        require(status == "UNSUPPORTED", "wrong bank status")
        keys(response, base | {"reason"}, "unsupported bank")
        require(response["supplied_trace_checked"] is False, "unsupported bank promoted trace check")
        keys(response["reason"], {"first_algebraic_variable", "kind"}, "algebraic unsupported reason")
        index = nat(response["reason"]["first_algebraic_variable"], "unsupported variable", len(request["values"]) - 1)
        require(request["values"][index]["kind"] == "ALGEBRAIC"
                and all(v["kind"] == "RATIONAL" for v in request["values"][:index]), "wrong first algebraic variable")
        require(type(response["reason"]["kind"]) is str, "wrong unsupported reason kind")
    return status


def parse_outcomes(rows, request):
    require(type(rows) is list and 1 <= len(rows) <= 15, "wrong number of four-copy rooted outcomes")
    context = request["context"]
    output, probabilities, previous = {}, {}, None
    for row in rows:
        keys(row, {"tree", "edge_polynomial", "probability"}, "rooted outcome")
        name = row["tree"]
        parse_tree(name, context["global_labels"])
        require(previous is None or previous < name, "rooted outcomes not unique lex order")
        previous = name
        terms = row["edge_polynomial"]
        require(type(terms) is list and 1 <= len(terms) <= 65536, "wrong rooted sparse term count")
        polynomial, prior = {}, None
        for term in terms:
            require(type(term) is list and len(term) == 2, "wrong rooted term pair")
            powers = term[0]
            require(type(powers) is list and len(powers) == len(context["edges"]), "wrong whole-edge polynomial dimension")
            for power in powers:
                nat(power, "whole-edge exponent", 4096)
            require(prior is None or prior < powers, "whole-edge terms not unique lex order")
            prior = powers
            coefficient = rational(term[1], 4096)
            require(coefficient != 0, "zero rooted sparse coefficient")
            polynomial[tuple(powers)] = coefficient
        output[name] = polynomial
        probability = rational(row["probability"], 4096)
        require(0 <= probability <= 1, "probability outside unit interval")
        probabilities[name] = probability
    require(sum(probabilities.values(), Fraction(0)) == 1, "rooted probabilities do not sum exactly to one")
    return output, probabilities


def verify_response(raw_request, raw_response, exit_code=None):
    request = parse_request(raw_request)
    response = json_frame(raw_response, MAX_CERTIFICATE_BYTES)
    common = {"verification_schema": "source_fit_reference_check_v1", "result_valid": True,
              "request_sha256": hashlib.sha256(raw_request).hexdigest(),
              "response_sha256": hashlib.sha256(raw_response).hexdigest(),
              "independent_all_coefficients_checked": False, "independent_probabilities_checked": False,
              "supplied_trace_arithmetic_checked": False, "request_echo_checked": False,
              "provider_work_checked": False, "bank_metadata_independently_checked": False,
              "resource_exhaustion_verified": False, "baseline_source_sha256": BASELINE_SHA,
              "baseline_called": False, "full_code_evaluated": False,
              "universal_native_refinement_verified": False,
              **{gate: False for gate in FALSE_GATES}}
    require(type(response) is dict, "response is not an object")
    if response.get("schema") == "source_fit_error_v1":
        keys(response, {"schema", "status", "code"}, "operational error frame")
        status = response["status"]
        require(status in ("INVALID_REQUEST", "INTERNAL", "EXECUTION_FAILURE", "UNKNOWN")
                and type(response["code"]) is str and 1 <= len(response["code"]) <= 128, "wrong operational error frame")
        require(exit_code in (None, 2 if status == "UNKNOWN" else 1), "error status/exit mismatch")
        return common | {"status": status, "scope": "OPERATIONAL_FRAME_ONLY"}
    if response.get("schema") == "source_fit_bank_result_v1":
        status = check_bank_frame(request, response)
        require(status in ("UNKNOWN", "UNSUPPORTED"), "rooted reference requires a rooted TABLE envelope")
        require(exit_code in (None, 2), "bank status/exit mismatch")
        return common | {"status": status, "scope": "INPUT_BOUND_FRAME_ONLY", "request_echo_checked": True}
    require(response.get("schema") == "source_fit_rooted_result_v1"
            and response.get("observer") == "ROOTED_UNRANKED_COMPLETE", "wrong rooted response schema/observer")
    _false_flags(response, ROOTED_FALSE_GATES)
    require(check_bank_frame(request, response.get("bank_result")) == "SYMBOLIC_BANK", "rooted response has no successful bank")
    require(strict_equal(response.get("readout_request"), default_readout_request(len(request["context"]["hybrids"]))),
            "natural observer/program/effective limits changed")
    base = {"schema", "status", "observer", "bank_result", "readout_request", "work", *ROOTED_FALSE_GATES}
    status = response.get("status")
    if status in ("UNKNOWN", "UNSUPPORTED"):
        keys(response, base | ({"limit"} if status == "UNKNOWN" else {"reason"}), "incomplete rooted response")
        require(response["work"] == {} and exit_code in (None, 2), "incomplete response has work/status/exit mismatch")
        if status == "UNKNOWN":
            _limit(response["limit"])
        else:
            require(type(response["reason"]) is dict and type(response["reason"].get("kind")) is str,
                    "wrong rooted unsupported reason")
        return common | {"status": status, "scope": "INPUT_BOUND_FRAME_ONLY", "request_echo_checked": True}
    require(status == "TABLE" and exit_code in (None, 0), "rooted TABLE status/exit mismatch")
    keys(response, base | {"configurations", "mixture"}, "rooted TABLE")
    require(request["terminal"] == "ANCESTRAL_COMPLETE" and request["context"]["local_samples"],
            "rooted TABLE must use nonempty completed natural panel")
    values = check_supplied_trace(request)
    configurations = response["configurations"]
    require(type(configurations) is list and len(configurations) == 1, "natural result has extra configurations")
    configuration = configurations[0]
    keys(configuration, {"label", "weight", "forcing", "outcomes"}, "natural configuration")
    require(configuration["label"] == "natural" and configuration["weight"] == "1/1"
            and strict_equal(configuration["forcing"], [None] * len(request["context"]["hybrids"])),
            "natural configuration binding changed")
    require(strict_equal(configuration["outcomes"], response["mixture"]), "natural configuration and mixture differ")
    polynomials, probabilities = parse_outcomes(response["mixture"], request)
    keys(response["work"], {"word_rows", "monomial_contributions", "largest_normalized_terms", "arithmetic_steps"}, "work frame")
    for key, value in response["work"].items():
        nat(value, f"work.{key}")
    expected = reference_polynomials(request)
    require(polynomials == expected, "full rooted whole-edge coefficient table differs from inherited compiler")
    arithmetic = ExactArithmetic()
    edge_values = values[:len(request["context"]["edges"])]
    require(all(probabilities[name] == evaluate(polynomial, edge_values, arithmetic)
                for name, polynomial in expected.items()), "rooted rational probability differs from exact reference")
    mass = {}
    for polynomial in expected.values():
        for power, coefficient in polynomial.items():
            mass[power] = arithmetic.add(mass.get(power, Fraction(0)), coefficient)
            if mass[power] == 0:
                del mass[power]
    require(mass == {(0,) * len(edge_values): Fraction(1)}, "reference polynomial law does not normalize identically")
    return common | {"status": "TABLE", "scope": "NATURAL_COMPLETED_ROOTED_UNRANKED_COEFFICIENT_REFERENCE",
                     "request_echo_checked": True, "baseline_called": True,
                     "independent_all_coefficients_checked": True, "independent_probabilities_checked": True,
                     "supplied_trace_arithmetic_checked": True, "rooted_outcomes": len(expected),
                     "whole_edge_terms": sum(map(len, expected.values()))}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--request", type=Path, required=True)
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--exit-code", type=int, choices=(0, 1, 2))
    args = parser.parse_args()
    try:
        result = verify_response(read_bounded(args.request, MAX_REQUEST_BYTES),
                                 read_bounded(args.certificate, MAX_CERTIFICATE_BYTES), args.exit_code)
        code = 0
    except (ValueError, TypeError, KeyError, UnicodeError, OverflowError, RecursionError, OSError, ImportError) as error:
        result = {"verification_schema": "source_fit_reference_check_v1", "result_valid": False,
                  "error": str(error)[:512], "certificate_valid": False, "full_solver_verified": False}
        code = 1
    print(json.dumps(result, sort_keys=True, separators=(",", ":"), ensure_ascii=True))
    return code


if __name__ == "__main__":
    raise SystemExit(main())
