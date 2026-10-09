"""Bounded CPU/bit-size benchmark; no quantum or full-state materialization."""
from __future__ import annotations

from fractions import Fraction
import hashlib
import json
from math import comb
from pathlib import Path
import platform
import resource
import statistics
import sys
from time import perf_counter
import tracemalloc

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "applications/practical-solver"))
from forest_baseline import ForestGraph, HermitianDilation, count_polynomial


def bits(value):
    return max(abs(value.numerator).bit_length(), value.denominator.bit_length())


def shape(m, name):
    if name == "singletons":
        return tuple(range(1, m + 1))
    if name == "pairs":
        return tuple((i, i + 1) for i in range(1, m, 2))
    tree = 1
    for label in range(2, m + 1):
        tree = (tree, label)
    return (tree,)


def time_call(function, repetitions=3):
    elapsed = []
    result = None
    for _ in range(repetitions):
        start = perf_counter()
        result = function()
        elapsed.append(perf_counter() - start)
    return result, statistics.median(elapsed)


def digest_fraction(value):
    hasher = hashlib.sha256()
    for integer in (value.numerator, value.denominator):
        data = integer.to_bytes(max(1, (integer.bit_length() + 7) // 8), "big")
        hasher.update(len(data).to_bytes(8, "big"))
        hasher.update(data)
    return hasher.hexdigest()


def main():
    cases = []
    access = []
    benchmark_start = perf_counter()
    for m in (8, 16, 32, 64):
        graph = ForestGraph(m)
        dilation = HermitianDilation(graph)
        f = graph.singleton_forest
        code, encode_seconds = time_call(lambda: graph.encode(f))
        _, decode_seconds = time_call(lambda: graph.decode(code))
        _, first_forward_seconds = time_call(lambda: next(graph.forward_neighbors(f)))
        row = graph.encode(f)
        row_support, support_seconds = time_call(lambda: tuple(dilation.nonzero_entries(row)), repetitions=1)
        access.append({"m": m, "encoding_bits": graph.code_bits, "sparsity_bound": dilation.sparsity,
                       "materialized_row_entries": len(row_support), "encode_seconds_median3": encode_seconds,
                       "decode_seconds_median3": decode_seconds, "first_forward_seconds_median3": first_forward_seconds,
                       "one_hermitian_row_seconds": support_seconds, "full_forest_graph_materialized": False})
        for survival_bits in (8, 32, 64):
            x = Fraction((1 << survival_bits) - 1, 1 << survival_bits)
            for name in ("singletons", "pairs", "comb"):
                f = shape(m, name)
                repetitions = 3 if m <= 32 else 1
                probability, seconds = time_call(lambda: graph.probability(f, x), repetitions)
                if not 0 < probability <= 1:
                    raise ArithmeticError("Strict-survival coordinate is not positive.")
                tracemalloc.start()
                replay = graph.probability(f, x)
                _, peak_bytes = tracemalloc.get_traced_memory()
                tracemalloc.stop()
                if replay != probability:
                    raise ArithmeticError("Memory replay changed the exact result.")
                coefficients = count_polynomial(m, len(f))
                peak_power_bits, peak_term_bits, peak_partial_sum_bits = 0, 0, 0
                partial_sum = Fraction(0)
                for exponent, coefficient in coefficients:
                    power = x**exponent
                    term = coefficient * power
                    partial_sum += term
                    peak_power_bits = max(peak_power_bits, bits(power))
                    peak_term_bits = max(peak_term_bits, bits(term))
                    peak_partial_sum_bits = max(peak_partial_sum_bits, bits(partial_sum))
                history = graph.history_statistics(f)
                cases.append({"m": m, "forest_shape": name, "roots": len(f),
                              "survival_numerator_bits": x.numerator.bit_length(), "survival_denominator_bits": x.denominator.bit_length(),
                              "degree_bound": comb(m, 2), "count_polynomial_terms": len(coefficients),
                              "coefficient_max_bits": max(bits(c) for _, c in coefficients),
                              "history_bits": history.histories.bit_length(), "hook_product_bits": history.hook_product.bit_length(),
                              "peak_power_bits": peak_power_bits, "peak_term_bits": peak_term_bits,
                              "peak_partial_count_sum_bits": peak_partial_sum_bits,
                              "result_numerator_bits": probability.numerator.bit_length(), "result_denominator_bits": probability.denominator.bit_length(),
                              "probability_seconds_median": seconds, "timing_repetitions": repetitions,
                              "peak_traced_probability_bytes_separate_replay": peak_bytes, "exact_probability_sha256": digest_fraction(probability)})
    result = {"status": "PASS", "evidence_tier": "authored_execution", "python": platform.python_version(),
              "platform": platform.platform(), "process_peak_rss_KiB_linux": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
              "elapsed_seconds": perf_counter() - benchmark_start, "access_cases": access, "probability_cases": cases,
              "method": "Untraced median wall timings; m64 once. Separate tracemalloc replay measures Python allocations. Exact rational input, coefficient, power, partial-sum and result bits charged. No process startup/import in probability timings.",
              "limitations": "Bounded measurements, not an asymptotic exponent or quantum comparison. No full forest graph, reversible circuit, quantum simulator, measurement/readout or source-feasibility backend executed."}
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
