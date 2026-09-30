#!/usr/bin/env python3
"""Exact endpoint checks for a declared finite extension, not the source's full model.

N diploids in each of two demes exchange exactly k uniformly sampled individuals.
Viability-weighted independent gametes make N random-mating offspring per deme.
The selected-locus check has no mutation. At the complete adaptive-reset endpoint,
the marker marginal closes because reset occurs after selection and birth.
Only N=2, k=1, s=1/3 is exhaustively enumerated here; no all-N claim follows.
"""

from fractions import Fraction as F
from hashlib import sha256
from itertools import product
from math import comb, factorial
from pathlib import Path
import json


N, K, S = 2, 1, F(1, 3)
COUNTS = tuple((a, b, N-a-b) for a in range(N+1) for b in range(N-a+1))
STATES = tuple(product(COUNTS, repeat=2))
INDEX = {state: i for i, state in enumerate(STATES)}
ZERO = (N, 0, 0)
ONE = (0, 0, N)
ABSORBING = {INDEX[(ZERO, ZERO)], INDEX[(ONE, ONE)]}


def copies(counts):
    return counts[1] + 2*counts[2]


def exchange_options(counts):
    """Exact multivariate hypergeometric sampling without replacement."""
    for picked in product(*(range(x+1) for x in counts)):
        if sum(picked) == K:
            probability = F(1, comb(N, K))
            for n, j in zip(counts, picked):
                probability *= comb(n, j)
            yield picked, probability


def after_exchange(local, outbound, inbound):
    return tuple(a-x+y for a, x, y in zip(local, outbound, inbound))


def births(p):
    """N independent Hardy-Weinberg diploid births from gamete frequency p."""
    genotype_p = ((1-p)**2, 2*p*(1-p), p**2)
    result = {}
    for counts in COUNTS:
        value = F(factorial(N))
        for count, probability in zip(counts, genotype_p):
            value /= factorial(count)
            value *= probability**count
        result[counts] = value
    assert sum(result.values()) == 1
    return result


def selected_gamete(counts, deme):
    weights = (1-S, 1-S/2, F(1)) if deme == 0 else (F(1), 1-S/2, 1-S)
    denominator = 2*sum(n*w for n, w in zip(counts, weights))
    return sum(g*n*w for g, (n, w) in enumerate(zip(counts, weights)))/denominator


def matrix(kind):
    result = []
    for a, b in STATES:
        row = [F(0) for _ in STATES]
        for (x, px), (y, py) in product(exchange_options(a), exchange_options(b)):
            if kind == "selected_no_mutation":
                probabilities = (selected_gamete(after_exchange(a, x, y), 0),
                                 selected_gamete(after_exchange(b, y, x), 1))
            elif kind == "marker_reset_after_selection":
                denominator = 2*(N-K*S)
                probabilities = ((copies(a)-copies(x)+(1-S)*copies(y))/denominator,
                                 (copies(b)-copies(y)+(1-S)*copies(x))/denominator)
            elif kind == "marker_neutral":
                probabilities = (F(copies(after_exchange(a, x, y)), 2*N),
                                 F(copies(after_exchange(b, y, x)), 2*N))
            else:
                raise ValueError(kind)
            for (aa, p_a), (bb, p_b) in product(births(probabilities[0]).items(),
                                               births(probabilities[1]).items()):
                row[INDEX[(aa, bb)]] += px*py*p_a*p_b
        assert sum(row) == 1
        assert all(x >= 0 for x in row)
        result.append(row)
    return result


def absorption_check(transition):
    actual = {i for i, row in enumerate(transition) if row[i] == 1}
    assert actual == ABSORBING
    reachable = set(actual)
    while True:
        expanded = reachable | {i for i, row in enumerate(transition)
                                if any(row[j] > 0 for j in reachable)}
        if expanded == reachable:
            break
        reachable = expanded
    assert len(reachable) == len(STATES)
    return {"absorbing_states": sorted(actual), "states_reaching_absorption": len(reachable)}


def advance(distribution, transition):
    return [sum(distribution[i]*transition[i][j] for i in range(len(STATES)))
            for j in range(len(STATES))]


def expectation(distribution, function):
    return sum(p*function(state) for p, state in zip(distribution, STATES))


def allele_mean(state):
    return F(sum(map(copies, state)), 4*N)


def global_allelic_diversity(state):
    p = allele_mean(state)
    return 2*p*(1-p)


def fraction_summary(value, full=False):
    out = {"decimal": float(value), "numerator_bits": value.numerator.bit_length(),
           "denominator_bits": value.denominator.bit_length(),
           "fraction_sha256": sha256(str(value).encode()).hexdigest()}
    if full:
        out["exact"] = str(value)
    return out


def matrix_digest(transition):
    encoded = "\n".join(",".join(str(x) for x in row) for row in transition)
    return sha256(encoded.encode()).hexdigest()


def solve_absorption(transition):
    """Exact Gaussian elimination: all-ONE fixation probability and mean hit time."""
    transient = sorted(set(range(len(STATES))) - ABSORBING)
    fixed_one = INDEX[(ONE, ONE)]
    rows = [[F(i == j)-transition[i][j] for j in transient]
            + [transition[i][fixed_one], F(1)] for i in transient]
    size = len(transient)
    for column in range(size):
        pivot = next(i for i in range(column, size) if rows[i][column] != 0)
        rows[column], rows[pivot] = rows[pivot], rows[column]
        scale = rows[column][column]
        rows[column] = [x/scale for x in rows[column]]
        for i in range(size):
            if i != column and rows[i][column] != 0:
                scale = rows[i][column]
                rows[i] = [x-scale*y for x, y in zip(rows[i], rows[column])]
    probability = [F(0)]*len(STATES)
    time = [F(0)]*len(STATES)
    probability[fixed_one] = F(1)
    for i, row in zip(transient, rows):
        probability[i], time[i] = row[-2:]
    for i in transient:
        assert probability[i] == sum(transition[i][j]*probability[j] for j in range(len(STATES)))
        assert time[i] == 1+sum(transition[i][j]*time[j] for j in range(len(STATES)))
    return probability, time


def pulse_distribution(reset_before_selection=False):
    """The first k immigrants into deme 2 are BB; all other individuals are bb."""
    p = F(K, N) if reset_before_selection else K*(1-S)/(N-K*S)
    distribution = [F(0)]*len(STATES)
    for count, probability in births(p).items():
        distribution[INDEX[(ZERO, count)]] = probability
    return distribution


def boundary_checks():
    """Concrete witnesses explaining why the theorem's exclusions matter."""
    global K, S
    saved_k, saved_s = K, S
    mirror = INDEX[(ONE, ZERO)]
    reverse = INDEX[(ZERO, ONE)]
    out = {}
    try:
        K = 0
        isolated = matrix("selected_no_mutation")
        assert isolated[mirror][mirror] == 1
        out["k_zero"] = "Oppositely fixed demes stay fixed; global absorption claim fails, and pulse B0=0."
        K = N
        swapping = matrix("selected_no_mutation")
        assert swapping[mirror][reverse] == swapping[reverse][mirror] == 1
        out["k_equals_N"] = "Oppositely fixed demes form a deterministic two-cycle; global absorption fails."
        K, S = saved_k, F(0)
        reset = matrix("marker_reset_after_selection")
        distribution = pulse_distribution()
        assert expectation(distribution, allele_mean) == F(K, 2*N)
        assert expectation(advance(distribution, reset), allele_mean) == F(K, 2*N)
        out["s_zero"] = "Complete reset has expected RI=0, matching the endpoint formula."
        S = F(1)
        try:
            selected_gamete(ONE, 1)
        except ZeroDivisionError:
            out["s_one"] = "An entirely maladapted deme has zero total viability; the declared sampler is undefined."
        else:
            raise AssertionError("Zero-viability exclusion was not exercised")
    finally:
        K, S = saved_k, saved_s
    return out


def main():
    selected = matrix("selected_no_mutation")
    reset = matrix("marker_reset_after_selection")
    neutral = matrix("marker_neutral")
    matrices = {"selected_no_mutation": selected,
                "marker_reset_after_selection": reset, "marker_neutral": neutral}
    results = {"model": "declared finite extension; exact endpoint marginals only",
               "parameters": {"N_per_deme": N, "k_exchange": K, "s": str(S),
                              "m": str(F(K, N))},
               "state_count": len(STATES), "genotype_count_states": len(COUNTS),
               "state_order": STATES, "matrices": {}}
    for name, transition in matrices.items():
        results["matrices"][name] = {"row_sums_exactly_one": True,
                                   "sha256": matrix_digest(transition),
                                   **absorption_check(transition)}
    for transition in (reset, neutral):
        for i, row in enumerate(transition):
            assert expectation(row, allele_mean) == allele_mean(STATES[i])
    results["marker_martingale_all_36_rows"] = {"reset_after_selection": True, "neutral": True}

    mirror = INDEX[(ONE, ZERO)]
    distribution = [F(0)]*len(STATES)
    distribution[mirror] = F(1)
    results["selected_H_from_mirrored_pure_initial_state"] = {"0": fraction_summary(F(1, 2), True)}
    for horizon in range(1, 11):
        distribution = advance(distribution, selected)
        if horizon in (1, 2, 5, 10):
            if horizon == 1:
                assert expectation(distribution, global_allelic_diversity) == F(11, 25)
            results["selected_H_from_mirrored_pure_initial_state"][str(horizon)] = fraction_summary(
                expectation(distribution, global_allelic_diversity), horizon <= 2)
    probability, times = solve_absorption(selected)
    assert probability[mirror] == F(1, 2)
    results["selected_absorption_from_mirror"] = {
        "all_EE_probability": str(probability[mirror]),
        "expected_generations": fraction_summary(times[mirror], True),
        "linear_system_residual_exactly_zero_all_transient_states": True}

    baseline = F(K, 2*N)
    expected_ri = S*(1-F(K, N))/(1-F(K, N)*S)
    results["pulse_marker_baseline_B0"] = str(baseline)
    results["pulse_endpoint_checks"] = {}
    for name, initial, transition, wanted in (
            ("reset_after_selection", pulse_distribution(), reset, expected_ri),
            ("reset_before_selection_timing_control", pulse_distribution(True), neutral, F(0)),
            ("reset_after_selection_but_initial_background_globally_EE", pulse_distribution(True), reset, F(0)),
            ("genetic_globally_fixed_selected_background", pulse_distribution(True), neutral, F(0))):
        distribution = initial
        horizon_results = {}
        for horizon in range(1, 11):
            value = expectation(distribution, allele_mean)
            ri = 1-value/baseline
            assert ri == wanted
            if horizon in (1, 2, 5, 10):
                horizon_results[str(horizon)] = {"expected_B": str(value), "expected_RI": str(ri)}
            distribution = advance(distribution, transition)
        results["pulse_endpoint_checks"][name] = horizon_results
    assert expected_ri == F(1, 5)
    results["boundary_checks"] = boundary_checks()
    results["scope_limits"] = [
        "Exhaustive finite-state checks cover only N=2, k=1, s=1/3.",
        "Selected-locus and marker-only projections close only at the declared endpoints.",
        "Intermediate epimutation, a full two-locus chain, and a monotone finite-size effect are not tested.",
        "Balanced exact exchange, positive fitness, and independent gamete births are model assumptions.",
        "Early-reset control changes lifecycle order; it is not an alternative fit of the same model.",
        "Globally EE initialization has equal viability within each deme at the pulse; the reset formula requires a previously reset-compatible background.",
        "Absorption graph and exact linear solve are finite-case checks, not an all-N computer proof."]
    output = Path(__file__).with_name("exact_results.json")
    output.write_text(json.dumps(results, indent=2)+"\n")
    print(json.dumps({"output": str(output), "states": len(STATES),
                      "matrices": {name: item["sha256"] for name, item in results["matrices"].items()},
                      "expected_H": {t: item["decimal"] for t, item in results["selected_H_from_mirrored_pure_initial_state"].items()},
                      "mean_absorption_generations": float(times[mirror]),
                      "after_reset_RI": str(expected_ri), "checks": "all exact assertions passed"}, indent=2))


if __name__ == "__main__":
    main()
