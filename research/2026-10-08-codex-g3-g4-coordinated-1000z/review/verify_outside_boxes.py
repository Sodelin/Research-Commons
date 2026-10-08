"""Independent static rational audits; no author/provider module execution."""
from pathlib import Path
from fractions import Fraction as F
from math import comb
import datetime
import hashlib
import json
import sys

sys.set_int_max_str_digits(0)
ROOT = Path(__file__).resolve().parents[3]
BASE = ROOT / "research/2026-10-08-codex-g3-g4-coordinated-1000z"
P = BASE / "g4-forest/outside-box-continuation"


class I:
    def __init__(self, a, b=None):
        self.a, self.b = F(a), F(a if b is None else b)
        assert self.a <= self.b
    def __add__(self, o):
        o = o if isinstance(o, I) else I(o)
        return I(self.a + o.a, self.b + o.b)
    __radd__ = __add__
    def __neg__(self):
        return I(-self.b, -self.a)
    def __sub__(self, o):
        return self + -(o if isinstance(o, I) else I(o))
    def __rsub__(self, o):
        return I(o) - self
    def __mul__(self, o):
        o = o if isinstance(o, I) else I(o)
        v = [a * b for a in (self.a, self.b) for b in (o.a, o.b)]
        return I(min(v), max(v))
    __rmul__ = __mul__
    def __truediv__(self, o):
        o = o if isinstance(o, I) else I(o)
        assert not o.a <= 0 <= o.b
        return self * I(1 / o.b, 1 / o.a)
    def __rtruediv__(self, o):
        return I(o) / self
    def __pow__(self, k):
        assert self.a >= 0 and k >= 0 and isinstance(k, int)
        return I(self.a ** k, self.b ** k)
    def mag(self):
        return max(abs(self.a), abs(self.b))
    def contains(self, o):
        return self.a <= o.a and o.b <= self.b
    def encoded(self):
        return [str(self.a), str(self.b)]


def read(path):
    raw = path.read_bytes()
    return raw, hashlib.sha256(raw).hexdigest()


def capture(path):
    raw, sha = read(path)
    return json.loads(raw), sha


def add(a, b, scale=F(1)):
    c = dict(a)
    for k, v in b.items():
        c[k] = c.get(k, F()) + scale * v
    return {k: v for k, v in c.items() if v}


def mul(a, b):
    c = {}
    for (t, x, w), v in a.items():
        for (s, y, z), u in b.items():
            if t + s <= 6:
                key = t + s, x + y, w + z
                c[key] = c.get(key, F()) + v * u
    return {k: v for k, v in c.items() if v}


def source_log(n):
    # Direct two-arm binomial expansion. Odd powers of the arm difference
    # cancel under k <-> n-k; no provider polynomial or code is imported.
    b = {}
    for k in range(n + 1):
        a, c = k * (k - 1) // 2, (n - k) * (n - k - 1) // 2
        for j in range(3):
            h = 2 * j
            if h > a + c:
                continue
            coeff = sum(comb(a, i) * comb(c, h - i) * (-1) ** (h - i)
                        for i in range(max(0, h - c), min(a, h) + 1))
            for v in range(min(a + c - h, 6 - 3 * j) + 1):
                key = v + 3 * j, v, j
                b[key] = b.get(key, F()) + F(comb(n, k), 2 ** n) * coeff * comb(a + c - h, v) * (-1) ** v
    x = add(b, {(0, 0, 0): F(-1)})
    assert x.get((0, 0, 0), 0) == 0
    power, answer = {(0, 0, 0): F(1)}, {}
    for j in range(1, 7):
        power = mul(power, x)
        answer = add(answer, power, F((-1) ** (j + 1), j))
    return answer


def trim(a):
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def uadd(a, b, scale=F(1)):
    c = [F()] * max(len(a), len(b))
    for i, v in enumerate(a):
        c[i] += v
    for i, v in enumerate(b):
        c[i] += scale * v
    return trim(c)


def umul(a, b):
    c = [F()] * (len(a) + len(b) - 1)
    for i, v in enumerate(a):
        for j, w in enumerate(b):
            c[i + j] += v * w
    return trim(c)


def value(a, x):
    ans = F()
    for v in reversed(a):
        ans = ans * x + v
    return ans


def rem(a, b):
    a = list(a)
    while len(a) >= len(b) and any(a):
        step = len(a) - len(b)
        factor = a[-1] / b[-1]
        for i, v in enumerate(b):
            a[i + step] -= factor * v
        trim(a)
    return a


def changes(sequence, x):
    vals = [value(a, x) for a in sequence]
    signs = [(v > 0) - (v < 0) for v in vals if v]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def jet_and_roots():
    saved, sha = capture(P / "EXACT-LEADING-SIXTH-SIGN.json")
    jet = {}
    for n, w in ((6, 1), (5, -6), (4, 15), (3, -20), (2, 15)):
        jet = add(jet, source_log(n), F(w))
    assert jet == {(6, 6, 0): F(15, 16), (6, 3, 1): F(-45, 4)}
    assert jet == {tuple(x["exponents"]): F(x["coefficient"]) for x in saved["D6_jet_through_t6"]}
    roots = []
    for row in saved["exact_leading_root_isolations"]:
        y = 1 + F(row["delta"])
        S4 = [1 + y ** 4, 0, 0, 0, F(2)]
        S5 = [1 + y ** 5, 0, 0, 0, 0, F(2)]
        H2, H1 = [-1 - 2 * y ** 2, 0, F(3)], [-1 - 2 * y, F(3)]
        G = uadd([30 * x for x in umul(S4, H2)], umul(S5, H1), F(-48))
        assert G == list(map(F, row["G_coefficients_ascending"]))
        sturm = [G, [i * G[i] for i in range(1, len(G))]]
        while len(sturm[-1]) > 1:
            sturm.append([-x for x in rem(sturm[-2], sturm[-1])])
        assert sturm == [list(map(F, x)) for x in row["sturm_sequence_coefficients_ascending"]]
        assert changes(sturm, F(9, 5)) - changes(sturm, F(2)) == 1
        lo, hi = map(F, row["unique_root_isolating_interval"])
        assert y < lo < hi < 2
        assert changes(sturm, lo) - changes(sturm, hi) == 1
        roots.append({"delta": row["delta"], "unique_root_in_9over5_to_2": True, "saved_interval_verified": True})
    assert F(1, 64) - F(1, 10) ** 2 / 8 == F(23, 1600)
    return {"receipt_sha256": sha, "jet_matches": True, "independent_method": "direct arm binomial expansion followed by formal log in Q[t,A,w]", "roots": roots}


def box(case):
    doc, inp = capture(P / f"CASE-{case}-RATIONAL-BOX.json")
    cert, csha = capture(P / f"CASE-{case}-INTERVAL-CERTIFICATE.json")
    six, ssha = capture(P / f"CASE-{case}-CAP6-CUBE.json")
    assert cert["input_sha256"] == six["input_sha256"] == inp
    assert six["cap5_certificate_sha256"] == csha
    assert cert["own_source_sha256"] == "861766646095eb5346529216e679a5851d5dd84e2f5c0a8d969d1dc748b26497"
    assert six["executed_full6_source_extension_sha256"] == "e2acfabf1b152244b2a75290c7ccefc8f3bfb9ff4727687986c14f2c19cdc736"
    r = F(doc["parameter_cube_radius"])
    C = [[F(x) for x in row] for row in cert["explicit_rational_preconditioner_C"]]
    J = [[I(*x) for x in row] for row in cert["complete_Jacobian_interval_on_cube"]]
    Fc = [I(*x) for x in cert["center_F_interval"]]
    assert len(C) == len(J) == len(Fc) == 8 and all(len(row) == 8 for row in C + J)
    E = [[I(int(i == j)) - sum((C[i][k] * J[k][j] for k in range(8)), I(0))
          for j in range(8)] for i in range(8)]
    for i in range(8):
        for j in range(8):
            assert I(*cert["identity_minus_CJ_interval"][i][j]).contains(E[i][j])
    q = max(sum(v.mag() for v in row) for row in E)
    assert q <= F(cert["contraction_infinity_norm_upper_bound_exact_rational"]) < F(1, 2)
    CF = [sum((C[i][j] * Fc[j] for j in range(8)), I(0)) for i in range(8)]
    displacement = max(v.mag() for v in CF)
    assert displacement <= F(cert["center_displacement_infinity_upper_bound_exact_rational"]) < r / 4
    M = F(cert["M_conservative_exact_rational"])
    eta = F(cert["certified_target_scaled_coordinate_radius_exact_rational"])
    assert M >= max(F(1), *(sum(abs(x) for x in row) for row in C))
    assert eta == r / (4 * M) and q * r + displacement + M * eta < r
    fixed = doc["fixed_rational_source"]
    t, d = F(fixed["t"]), F(fixed["d"])
    AA = list(map(F, fixed["means"]))
    W = [I(F(x) - r, F(x) + r) for x in doc["approximate_rational_parameters"][:3]] + [I(fixed["w4"])]
    qq = [1 - A * t / 2 for A in AA]
    assert d == F(1, 4) and F(fixed["a"]) * F(fixed["b"]) == d
    answer = I(1)
    for k, (A, w) in enumerate(zip(AA, W)):
        s, h2 = I(1 - A * t), w * t ** 3
        gates = [w, s, h2, s * s - h2, I((A * t) ** 2) - h2]
        for j, gate in enumerate(gates):
            bound = I(*cert["arm_strictness_gate_intervals"][k][j])
            assert bound.contains(gate) and bound.a > 0
        assert I(*cert["arm_strictness_gate_intervals"][k][1]).b < 1
        b6 = I(0)
        xy = s * s - h2
        for count in range(4):
            a, b = count * (count - 1) // 2, (6 - count) * (5 - count) // 2
            lo, diff = min(a, b), abs(a - b)
            term = xy ** lo if count == 3 else 2 * xy ** lo * sum((
                comb(diff, 2 * j) * s ** (diff - 2 * j) * h2 ** j
                for j in range(diff // 2 + 1)), I(0))
            b6 += comb(6, count) * term / 64
        answer *= (b6 / qq[k] ** 15) ** 2
    theta = [I(F(x) - r, F(x) + r) for x in doc["approximate_rational_parameters"][3:]]
    X1, X2, X3, X6, X7 = theta
    a, b, U, seam = [F(fixed[k]) for k in ("a", "b", "U", "seam")]
    X4, X5 = qq[0] * seam / b, 1 / (b * seam)
    edges = [I(a * b * U / qq[2]), X7 / (qq[1] * U), X6 / (qq[3] * X7), I(X5) / (qq[0] * X6), I(seam),
             I(seam), X3 / (qq[3] * X4), X2 / (qq[1] * X3), X1 / (qq[2] * X2), 1 / X1]
    for ref, got in zip(edges, cert["ordinary_edge_interval_bounds_exact_rational"]):
        bound = I(*got)
        assert bound.contains(ref) and 0 < bound.a <= bound.b < 1
    bound = I(*cert["ninth_leading_edge_interval_exact_rational"])
    assert bound.contains(edges[0] * I(1 - r, 1 + r)) and 0 < bound.a <= bound.b < 1
    residual = d ** 15 * (answer - 1)
    saved = I(*six["tight_b6_minus_d15_interval"])
    assert residual.b < 0 and saved.b < 0
    assert max(residual.a, saved.a) <= min(residual.b, saved.b)
    allrows = six["full20_cube_residual_intervals"]
    assert len(allrows) == 20 and all(F(hi) < 0 or F(lo) > 0 for lo, hi in allrows)
    assert six["cap6_nine_free_residual_intervals"] == [allrows[i] for i in six["cap6_free_indices"]]
    for lo, hi in six["ordinary_edge_survival_intervals"]:
        assert 0 < F(lo) <= F(hi) < 1
    for cell in six["arm_inequality_intervals"]:
        assert all(0 < F(lo) <= F(hi) for lo, hi in cell) and F(cell[1][1]) < 1
    direct = I(*allrows[0])
    assert max(direct.a, saved.a) <= min(direct.b, saved.b)
    return {"case": case, "input_sha256": inp, "cap5_certificate_sha256": csha,
            "cap6_receipt_sha256": ssha, "exact_contraction_and_strict_domain_audit": True,
            "independent_sixth_diagonal_negative_interval": residual.encoded(),
            "saved_sixth_interval_overlaps_independent": True, "all20_saved_intervals_separate_zero": True}


def main():
    provider_pins = {
        "research/2026-10-01-g4-admitted-testers-0819z/forest_algebra.py": "850589b346a6cc000e102c594a1ebc6342e9e1ba4604edace20fe5ecdc385884",
        "research/2026-10-08-cloud-g4-eight-cell-0704z/ACTUAL-EIGHT-CELL-FULL-FIVE-RETURN.md": "20e6b92a6039db24faee986f354428d8936fb3b992d2eaec24192d538f50ae81",
        "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-forest/exact_forest_layer.py": "e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8",
        "research/2026-10-08-codex-g3-g4-coordinated-1000z/g4-forest/cap6_from_cap5_box.py": "e2acfabf1b152244b2a75290c7ccefc8f3bfb9ff4727687986c14f2c19cdc736",
        "research/2026-10-08-codex-g3-g4-coordinated-1000z/ROOT-CAP5-INTERVAL-REVIEW.md": "76712c4f36ef111e8cdce96eaa4906fa60788f21d8ed288f8e4749ddc065caef",
    }
    providers = []
    for path, expected in provider_pins.items():
        raw, sha = read(ROOT / path)
        assert sha == expected
        providers.append({"path": path, "sha256": sha, "bytes": len(raw), "match": True})
    manifest, msha = capture(P / "PUBLIC-FILES.json")
    auth = []
    for row in manifest["files"]:
        raw, sha = read(ROOT / row["path"])
        assert sha == row["sha256"] and len(raw) == row["bytes"]
        auth.append(row)
    prior = []
    for name, pin in manifest["prior_manifest_sha256"].items():
        old, sha = capture(BASE / "g4-forest" / name)
        assert sha == pin
        for row in old["files"]:
            raw, digest = read(ROOT / row["path"])
            assert digest == row["sha256"] and len(raw) == row["bytes"]
            prior.append(row["path"])
    result = {"schema": "reviewer-outside-box-static-source-audit-v1", "utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "manifest_sha256": msha, "authenticated_new_objects": auth, "provider_pins": providers,
              "prior_frozen_objects_unchanged": len(prior), "jet_and_roots": jet_and_roots(),
              "boxes": [box("01"), box("02")], "inherited_or_author_code_executed": False,
              "scope": "Exact saved contraction/source-domain bound arithmetic, independently expanded source jet/Sturm chains and rational six-diagonal cubes. Jacobian/other full-row enclosures rely on separately reviewed unchanged outward interval source provider, not a new replay."}
    dest = Path(__file__).with_name("G4-OUTSIDE-BOX-STATIC-VERIFICATION.json")
    dest.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": "PASS", "new_objects": len(auth), "prior_objects": len(prior), "boxes": 2, "output": str(dest)}))


if __name__ == "__main__":
    main()
