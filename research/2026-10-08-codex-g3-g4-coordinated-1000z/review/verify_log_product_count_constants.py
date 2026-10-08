"""Reviewer-owned static rational audit; imports or executes no provider code."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import subprocess

REPO = Path(__file__).resolve().parents[3]
PACKET = REPO / "research/2026-10-08-codex-g3-g4-coordinated-1000z/g3-coupled"
OUT = Path(__file__).with_name("G3-LOG-PRODUCT-STATIC-VERIFICATION.json")


def read(path):
    b = path.read_bytes()
    return b, hashlib.sha256(b).hexdigest()


def loss(z, order=4):
    assert 0 <= z < 1
    a = sum((z ** k / k for k in range(1, order + 1)), Q())
    return a, a + z ** (order + 1) / ((order + 1) * (1 - z))


def combine(weights, boxes):
    lo = hi = Q()
    for w, (a, b) in zip(weights, boxes):
        x, y = w * a, w * b
        lo += min(x, y)
        hi += max(x, y)
    return lo, hi


def polyadd(a, b, scale=Q(1)):
    c = dict(a)
    for k, v in b.items():
        c[k] = c.get(k, Q()) + scale * v
    return {k: v for k, v in c.items() if v}


def polymul(a, b):
    c = {}
    for (i, j), v in a.items():
        for (k, l), w in b.items():
            key = i + k, j + l
            c[key] = c.get(key, Q()) + v * w
    return {k: v for k, v in c.items() if v}


def main():
    records = []
    pins = json.loads(read(PACKET / "LOG-PRODUCT-SOURCE-PINS.json")[0])["pins"]
    for pin in pins:
        raw, sha = read(REPO / pin["path"])
        assert sha == pin["sha256"] and len(raw) == pin["bytes"]
        committed = subprocess.run(["git", "show", "HEAD:" + pin["path"]], cwd=REPO,
                                   check=True, capture_output=True).stdout
        assert committed == raw
        blob = subprocess.run(["git", "rev-parse", "HEAD:" + pin["path"]], cwd=REPO,
                              check=True, capture_output=True, text=True).stdout.strip()
        records.append({"path": pin["path"], "sha256": sha, "bytes": len(raw),
                        "head_git_blob": blob, "match": True})
    cert_path = REPO / "research/2026-10-01-sol61-g3-boundary-resume-2124z/paired-normal-certificate.json"
    cert_raw, cert_sha = read(cert_path)
    assert cert_sha == "2a9a8ab705c7fb689b0cbbf3d15e6972ecd71fe837c8926344bb950aa4c5a118"
    cert = json.loads(cert_raw)
    c = cert["constants"]
    B0, B1, delta, gamma, cutoff, p0, eta, cs = [Q(c[k]) for k in (
        "B0", "B1", "delta", "gamma", "Q", "p0", "root_interval_half_width", "C_star")]
    outside = Q(c["outside_U_F0_lower_bound"])
    fpp = Q(cert["normal_records"]["F0"]["F_second_derivative_at_one"])
    normals = []
    for name in ("F0", "F1"):
        row = cert["normal_records"][name]
        normals.append(dict(zip(row["exponents"], map(Q, row["c"]))))
    lambdas = [1, 3, 6, 10, 15, 21]
    weights = [[row.get(l, Q()) for l in lambdas] for row in normals]
    def F(row, x):
        return sum((v * (1 - x ** l) for l, v in row.items()), Q())
    for row in normals:
        assert sum(row.values()) == 1
        assert sum(l * v for l, v in row.items()) == 0
        assert F(row, Q(1, 2)) == 0
    a0, a1 = F(normals[0], Q(1, 4)), F(normals[1], Q(1, 8))
    assert a0 > 0 and a1 > 0 and F(normals[1], Q(1, 4)) == 0
    assert gamma == a1 / 12
    kappa = min(outside / 12, fpp * cutoff ** 3 / 12)
    u = Q(1, 2) + eta
    C0 = min(cs, gamma * (1 - u) / (4 * B1 * (B0 / delta) ** 2))
    K, L = 2 * B1 / delta ** 2, 6 + B0 * p0 / kappa
    assert 0 < eta <= Q(1, 32) and u < cutoff < 1
    assert 0 < p0 <= Q(1, 2) and p0 <= outside / (2 * B0)
    assert C0 <= p0 * (1 - cutoff)
    assert 2 * B1 * (B0 / delta) ** 2 * C0 / (1 - u) <= gamma / 2
    n0 = 2 ** 200
    theta_max = Q(4, 2 ** 175)
    tau_max, p_max = theta_max + Q(1, n0), (theta_max + Q(1, n0)) / n0
    assert theta_max + Q(1, 2 * n0) + tau_max * p_max / (2 * (1 - p_max)) < C0
    assert B0 * p_max / (3 * (1 - p_max)) < a0 / 2
    rate = gamma * (Q(5, 8) - 2 * p_max / (1 - p_max)) ** 3 / (
        2 * L ** 3 * (a1 / 3 + B1 * p_max / 2 + K * B0 ** 2 * tau_max))
    assert rate > Q(1, 128 ** 2)
    saved = json.loads(read(PACKET / "log-product-count-test-receipt.json")[0])
    assert rate == Q(saved["rate_squared_exact"])
    # Full coefficient identity in Q[p,q], not finite sampled substitutions.
    one, p, q = {(0, 0): Q(1)}, {(1, 0): Q(1)}, {(0, 1): Q(1)}
    f1 = polyadd(polyadd(one, p, Q(-1)), polymul(p, q))
    f3 = polyadd(polyadd(one, p, Q(-1)), {(1, 3): Q(1)})
    left = polyadd(f3, polymul(polymul(f1, f1), f1), Q(-1))
    one_q = polyadd(one, q, Q(-1))
    bracket = polyadd(polyadd({(0, 0): Q(2)}, q), polymul(p, one_q), Q(-1))
    right = polymul(polymul(polymul(p, polyadd(one, p, Q(-1))),
                            polymul(one_q, one_q)), bracket)
    assert left == right
    fixtures = []
    theta_lo, theta_hi = (2 * x for x in loss(Q(1, 2 ** 175), order=3))
    for e in (200, 220, 240):
        n = 2 ** e
        def ceil(x):
            return -((-x.numerator) // x.denominator)
        k0, k1 = ceil(theta_lo * n), ceil(theta_hi * n)
        assert k0 == k1
        prob = Q(k0, n * n)
        boxes = [loss(prob * (1 - Q(1, 2) ** l)) for l in lambdas]
        aa = tuple(n * x for x in combine(weights[0], boxes))
        bb = tuple(n * x for x in combine(weights[1], boxes))
        dd = tuple(n * x for x in combine([3, -1], [boxes[0], boxes[1]]))
        lowerP = (dd[0] - aa[1] / kappa) / L
        upperE = bb[1] + K * max(abs(aa[0]), abs(aa[1])) ** 2
        assert aa[1] < 0 and lowerP > 0 and upperE > 0
        assert gamma * lowerP ** 3 / 2 > Q(n * n, 128 ** 2) * upperE
        existing = next(x for x in saved["fixtures"] if x["N"] == "2^" + str(e))
        assert k0 == int(existing["ceil_theta_times_N"])
        assert prob == Q(existing["factor_probability"])
        fixtures.append({"N": "2^" + str(e), "ceil_theta_N": str(k0),
                         "independent_log_series_order": 4, "strict_rate_gate": True})
    result = {"schema": "reviewer-log-count-static-rational-v1", "status": "PASS",
              "provider_pins": records, "symbolic_defect_identity": "complete Q[p,q] coefficient equality",
              "rate_matches_author_receipt": True, "rate_exceeds": "1/128^2",
              "second_L0_coefficient_at_half": "-F0(1/4)/2",
              "fixtures": fixtures, "provider_code_imported_or_executed": False,
              "huge_graph_or_expanded_observation_materialized": False,
              "scope": "Static rational premises and independent log intervals only; source inequalities and all-core count transfer require the accompanying hand review."}
    OUT.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "provider_pins": len(records), "fixtures": len(fixtures), "output": str(OUT)}))


if __name__ == "__main__":
    main()
