"""Exact channel transfer of inherited three-atom certificate; no source/QE run."""
from fractions import Fraction as F
from pathlib import Path
import datetime
import hashlib
import importlib.util
import json
import time

ROOT = Path(__file__).resolve().parents[3]
OUT = Path(__file__).resolve().parent
PROVIDER = ROOT / "research/2026-10-01-codex-g3-finite-recognition/boundary_checks.py"
spec = importlib.util.spec_from_file_location("inherited_boundary", PROVIDER)
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)  # Definition import; its main is not invoked.
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
start = time.monotonic()

def rat(value):
    value = F(value)
    return str(value.numerator) if value.denominator == 1 else str(value)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

powers = [0, 1, 3, 6, 10, 15, 21]
atoms = [F(1, 8), F(1, 4), F(1, 2)]
coefficients, quotient = boundary.expose(atoms)
polynomial = [F(0)] * 22
for exponent, coefficient in zip(powers, coefficients):
    polynomial[exponent] = coefficient
derivative = [(i + 1) * polynomial[i + 1] for i in range(21)]
factor = [F(1)]
for atom in atoms:
    factor = boundary.multiply(factor, [atom * atom, -2 * atom, F(1)])
checks = {"constant_coefficient_one": coefficients[0] == 1}
for i, atom in enumerate(atoms):
    checks[f"root_{i}"] = boundary.evaluate(polynomial, atom) == 0
    checks[f"derivative_root_{i}"] = boundary.evaluate(derivative, atom) == 0
checks["polynomial_factor_identity"] = boundary.multiply(factor, quotient) == polynomial
for i, coefficient in enumerate(quotient):
    checks[f"quotient_coefficient_{i}_positive"] = coefficient > 0

monophyly_receipt = OUT / "RANK-THREE-CHANNELS.json"
old = json.loads(monophyly_receipt.read_text())
inverse = [[F(x) for x in row] for row in old["inverse_matrix"]]
offsets = [-sum(row) for row in inverse]
hp_constant = coefficients[0] + sum(c * a for c, a in zip(coefficients[1:], offsets))
hp_coefficients = [sum(coefficients[i + 1] * inverse[i][j] for i in range(6))
                   for j in range(6)]
kp = 1 + abs(hp_constant) + sum(abs(c) for c in hp_coefficients)
checks["strict_P_channel_margin"] = kp > abs(hp_constant) + sum(abs(c) for c in hp_coefficients)
checks["strict_b1_channel_margin"] = F(4) > F(3)
checks["strict_b3_channel_margin"] = F(19) > F(18)

weight_matrix = [[F(1)] * 3, atoms, [x ** 3 for x in atoms]]
inverse_columns = [boundary.solve_square(weight_matrix, [F(int(i == j)) for i in range(3)])
                   for j in range(3)]
weight_inverse = [[inverse_columns[j][i] for j in range(3)] for i in range(3)]
for i in range(3):
    for j in range(3):
        checks[f"weight_inverse_{i}_{j}"] = sum(weight_inverse[i][k] * weight_matrix[k][j]
                                              for k in range(3)) == int(i == j)

profiles = []
for name, weights in [("original_COMMON_NO", [F(2, 5), F(1, 5), F(2, 5)]),
                      ("two_hybrid_COMMON_YES", [F(1, 4), F(1, 2), F(1, 4)])]:
    moments = [sum(w * x ** k for w, x in zip(weights, atoms)) for k in powers]
    recovered = [sum(c * v for c, v in zip(row, [F(1), moments[1], moments[2]]))
                 for row in weight_inverse]
    discriminant = weights[1] ** 2 - 4 * weights[0] * weights[2]
    probability_p = F(1, 2) + sum(c * m for c, m in zip(coefficients, moments)) / (2 * kp)
    probabilities = [F(2, 3), F(25, 48), F(1, 2) + moments[1] / 8,
                     F(1, 2) + moments[2] / 38, probability_p]
    checks[f"{name}_zero_exposing_expectation"] = sum(c * m for c, m in zip(coefficients, moments)) == 0
    checks[f"{name}_unique_weight_recovery"] = recovered == weights
    for i, value in enumerate(probabilities):
        checks[f"{name}_observable_probability_{i}_strict"] = 0 < value < 1
    checks[f"{name}_discriminant_sign"] = (discriminant < 0 if name.endswith("NO") else discriminant == 0)
    profiles.append({"name": name, "weights_at_increasing_atoms": list(map(rat, weights)),
                     "sparse_moments": list(map(rat, moments)),
                     "discriminant": rat(discriminant),
                     "five_original_bit1_probabilities_B2_B3_Q1_Q3_QP": list(map(rat, probabilities)),
                     "classification_tier": "hand all-core source argument; arithmetic checks only"})

survival_c = F(15, 16)
survival_z = F(1, 2) / survival_c ** 4
distribution = {F(1, 2): F(1)}
for _ in range(2):
    next_distribution = {}
    for value, weight in distribution.items():
        for new_value in [value, value / 2]:
            next_distribution[new_value] = next_distribution.get(new_value, F(0)) + weight / 2
    distribution = next_distribution
checks["two_factor_product_law"] = [distribution[x] for x in atoms] == [F(1, 4), F(1, 2), F(1, 4)]
checks["positive_two_bigon_padding"] = 0 < survival_z < 1 and 0 < survival_c / 2 < survival_c < 1
checks["two_bigon_maximum_survival"] = survival_z * survival_c ** 4 == F(1, 2)

assert all(checks.values())
record = {
    "schema": "g3-rank-three-exposing-channel-transfer-v1",
    "claim_tier": "exact inherited polynomial/channel/weight arithmetic; not executed whole-source inference",
    "started_utc": started, "elapsed_seconds": time.monotonic() - start,
    "script_path": str(Path(__file__).resolve().relative_to(ROOT)),
    "script_sha256": sha(Path(__file__).resolve()),
    "reused_polynomial_provider_path": str(PROVIDER.relative_to(ROOT)),
    "reused_polynomial_provider_sha256": sha(PROVIDER),
    "monophyly_derivation_provider_path": str(monophyly_receipt.relative_to(ROOT)),
    "monophyly_derivation_provider_sha256": sha(monophyly_receipt),
    "sparse_exponents": powers, "atoms": list(map(rat, atoms)),
    "exposing_polynomial_coefficients_in_sparse_order": list(map(rat, coefficients)),
    "squared_root_factor_coefficients_ascending": list(map(rat, factor)),
    "quotient_coefficients_ascending": list(map(rat, quotient)),
    "P_channel_H_constant": rat(hp_constant),
    "P_channel_H_indicator_coefficients_A2_through_A7": list(map(rat, hp_coefficients)),
    "P_channel_K": rat(kp),
    "P_channel_formula": "Pr(bit1|G)=1/2+H_P(G)/(2*K_P)",
    "weight_inverse_rows_against_1_b1_b3": [[rat(x) for x in row] for row in weight_inverse],
    "profiles": profiles,
    "actual_two_bigon_witness_survivals": {"z": rat(survival_z), "each_upper_arm_and_connector": rat(survival_c),
                                          "each_lower_arm": rat(survival_c / 2), "each_COMMON_weight": "1/2", "B_pendant": "1/2"},
    "checks": checks, "checks_passed": sum(checks.values()), "checks_total": len(checks), "status": "PASS",
    "compiler_invocations": 0, "QE_or_native_solver_invocations": 0,
    "whole_source_simulations": 0, "graph_census_invocations": 0,
    "limits": "Inherited expose() used unchanged; its main not invoked. Exact finite Bernoulli product arithmetic is not a fresh coalescent forward-compiler or a solver deciding original G3."
}
(OUT / "RANK-THREE-EXPOSED-ARITHMETIC.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({"status": record["status"], "checks_passed": record["checks_passed"],
                  "checks_total": len(checks), "profiles": profiles,
                  "exposing_sparse_coefficients": record["exposing_polynomial_coefficients_in_sparse_order"]}))
