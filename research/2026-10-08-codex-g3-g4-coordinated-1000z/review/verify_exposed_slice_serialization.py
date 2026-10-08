"""Independent exact arithmetic of saved data, without importing author code."""
from pathlib import Path
from fractions import Fraction as F
import datetime
import hashlib
import itertools
import json
import subprocess

ROOT = Path(__file__).resolve().parents[3]
PACKET = ROOT / "research/2026-10-08-codex-g3-g4-coordinated-1000z"
HERE = PACKET / "review"
S = PACKET / "g3-singular"

def captured(path):
    raw = path.read_bytes()
    return raw, hashlib.sha256(raw).hexdigest()

def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out

def val(poly, x):
    return sum(a * x**i for i, a in enumerate(poly))

raw, result_hash = captured(S / "RANK-THREE-EXPOSED-ARITHMETIC.json")
d = json.loads(raw)
raw, pins_hash = captured(S / "RANK-THREE-EXPOSED-SOURCE-PINS.json")
pins = json.loads(raw)
raw, inverse_hash = captured(S / "RANK-THREE-CHANNELS.json")
inverse = json.loads(raw)
checks = {}

def check(name, predicate):
    checks[name] = bool(predicate)
    assert predicate, name

atoms = list(map(F, d["atoms"]))
powers = d["sparse_exponents"]
coeff = list(map(F, d["exposing_polynomial_coefficients_in_sparse_order"]))
poly = [F(0)] * 22
for k, a in zip(powers, coeff):
    poly[k] = a
factor = [F(1)]
for a in atoms:
    factor = mul(factor, [a * a, -2 * a, F(1)])
quotient = list(map(F, d["quotient_coefficients_ascending"]))
check("squared_root_factor", factor == list(map(F, d["squared_root_factor_coefficients_ascending"])))
check("full_polynomial_product", mul(factor, quotient) == poly)
check("all_16_quotient_coefficients_positive", len(quotient) == 16 and all(x > 0 for x in quotient))
check("normalized_constant", poly[0] == 1)
for i, a in enumerate(atoms):
    check(f"double_root_{i}", val(poly, a) == val([j * x for j, x in enumerate(poly)][1:], a) == 0)
M = [list(map(F, row)) for row in inverse["original_transform_matrix"]]
B = [list(map(F, row)) for row in inverse["inverse_matrix"]]
for i in range(6):
    for j in range(6):
        check(f"monophyly_inverse_{i}_{j}", sum(B[i][k] * M[k][j] for k in range(6)) == (i == j))
H = [sum(coeff[i + 1] * B[i][j] for i in range(6)) for j in range(6)]
offset = coeff[0] - sum(H)
check("P_channel_coefficients", H == list(map(F, d["P_channel_H_indicator_coefficients_A2_through_A7"])))
check("P_channel_offset", offset == F(d["P_channel_H_constant"]))
K = F(d["P_channel_K"])
check("P_channel_strict_absolute_margin", K == 1 + abs(offset) + sum(map(abs, H)))
for bits in itertools.product([0, 1], repeat=6):
    probability = F(1, 2) + (offset + sum(x * b for x, b in zip(H, bits))) / (2 * K)
    check("channel_bit_" + "".join(map(str, bits)), 0 < probability < 1)
W = [list(map(F, row)) for row in d["weight_inverse_rows_against_1_b1_b3"]]
for i in range(3):
    for j in range(3):
        check(f"weight_inverse_{i}_{j}", sum(W[i][k] * atoms[j] ** [0, 1, 3][k] for k in range(3)) == (i == j))
for profile in d["profiles"]:
    name = profile["name"]
    weights = list(map(F, profile["weights_at_increasing_atoms"]))
    moments = [sum(w * a**k for a, w in zip(atoms, weights)) for k in powers]
    check(name + "_all_sparse_moments", moments == list(map(F, profile["sparse_moments"])))
    check(name + "_exposing_expectation", sum(c * b for c, b in zip(coeff, moments)) == 0)
    check(name + "_discriminant", weights[1] ** 2 - 4 * weights[0] * weights[2] == F(profile["discriminant"]))
    probabilities = [F(2, 3), F(25, 48), F(1, 2) + moments[1]/8, F(1, 2) + moments[2]/38, F(1, 2)]
    check(name + "_five_probabilities", probabilities == list(map(F, profile["five_original_bit1_probabilities_B2_B3_Q1_Q3_QP"])))
c = F(15, 16)
z = F(d["actual_two_bigon_witness_survivals"]["z"])
check("strict_positive_two_bigon_padding", 0 < z < 1 and z * c**4 == F(1, 2))

provider_rows = []
for row in pins["providers"] + pins["review_objects"]:
    path = ROOT / row["path"]
    raw, sha = captured(path)
    blob = subprocess.run(["git", "ls-tree", "HEAD", "--", row["path"]], cwd=ROOT, capture_output=True, text=True, check=True).stdout.split()
    good = sha == row["sha256"] and len(raw) == row["bytes"]
    check("source_identity_" + row["path"], good)
    provider_rows.append({"path": row["path"], "sha256": sha, "bytes": len(raw), "head_git_blob": blob[2] if blob else None, "match": good})

record = {"schema": "independent-exposed-slice-serialized-arithmetic-v1", "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "arithmetic_receipt_sha256": result_hash, "source_pins_sha256": pins_hash, "inverse_receipt_sha256": inverse_hash,
          "checks": checks, "checks_passed": len(checks), "provider_rows": provider_rows,
          "author_or_inherited_module_executions": 0, "compiler_QE_or_genealogy_executions": 0,
          "limits": "Saved JSON and source-byte arithmetic verified independently. Historical SourceFileLoader execution identity is not established; this check does not retroactively authenticate that execution."}
(HERE / "G3-EXPOSED-SLICE-STATIC-VERIFICATION.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({"status": "PASS", "checks": len(checks), "providers_and_objects": len(provider_rows)}))
