"""Actual full-six forest response on a declared nearby cap-five root cube.

Uses the immutable reviewed eight-cell interval provider and full-six source
extension. The root, rather than the rational candidate, is enclosed by all
reported cube intervals. This gate does not solve a new cap-six common zero.
"""
from __future__ import annotations
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import argparse
import json
import time
import types

PROVIDER_SHA = "861766646095eb5346529216e679a5851d5dd84e2f5c0a8d969d1dc748b26497"
FULL6_SHA = "e2acfabf1b152244b2a75290c7ccefc8f3bfb9ff4727687986c14f2c19cdc736"
HELPER_SHA = "e0ced6748fd6fbe27f8165446a1c63a09bdb598fd1bdcd89115d4ae4853193b8"


def captured(p, pin, name):
    raw = p.read_bytes()
    if sha256(raw).hexdigest() != pin:
        raise ValueError(f"authenticated source identity mismatch: {p}")
    m = types.ModuleType(name)
    m.__file__ = str(p)
    exec(compile(raw, str(p), "exec"), m.__dict__)
    return m


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, required=True)
    ap.add_argument("--input", type=Path, required=True)
    ap.add_argument("--certificate", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    if args.output.exists():
        raise ValueError("refusing to overwrite actual-source cube response")
    started = time.perf_counter()
    base = Path(__file__).resolve().parent
    raw = args.input.read_bytes()
    cert_raw = args.certificate.read_bytes()
    doc, cert = json.loads(raw), json.loads(cert_raw)
    input_sha = sha256(raw).hexdigest()
    declaration = json.loads((base/"INTERVAL-EXTENSION-DECLARATION.json").read_bytes())
    if input_sha not in [case["input_sha256"] for case in declaration["cases"]]:
        raise ValueError("cube was not declared for this bounded extension")
    if cert["status"] != "EXECUTED_OUTWARD_INTERVAL_CONTRACTION_GATE_PASS" or cert["input_sha256"] != input_sha:
        raise ValueError("matching cap-five contraction PASS required")
    if cert["own_source_sha256"] != PROVIDER_SHA:
        raise ValueError("matching immutable cap-five provider required")
    assert F(doc["fixed_rational_source"]["d"]) == F(1, 4)
    m = captured(base/"reviewed_interval_gate_frozen.py", PROVIDER_SHA, "reviewed_immutable_cap5_interval")
    full = captured(base.parent/"cap6_from_cap5_box.py", FULL6_SHA, "reviewed_immutable_full6_extension")
    h = captured(args.root/m.HELPER, HELPER_SHA, "authenticated_full_forest_helper")
    fa, original_sha = h.load_source(args.root)
    m.mp.mp.dps = m.mp.iv.dps = 160
    src = full.source_class(m, h, fa)(doc["fixed_rational_source"])
    radius = F(doc["parameter_cube_radius"])
    cube = [m.D(m.iv(v)+m.mp.iv.mpf([-1, 1])*m.iv(radius)) for v in doc["approximate_rational_parameters"]]
    row, residual, edges, arms, diagonal, score = src.complete(cube)
    physical = all(0 < m.endpoints(e.v)[0] <= m.endpoints(e.v)[1] < 1 for e in edges)
    physical = physical and all(all(m.endpoints(v)[0] > 0 for v in gates) and m.endpoints(gates[1])[1] < 1 for gates in arms)
    assert physical
    overlap = residual[0].v-diagonal.v
    assert m.endpoints(overlap)[0] <= 0 <= m.endpoints(overlap)[1]
    lower = [sum((F(c, 6)*v for c, v in zip(rr, residual)), m.D(0)) for rr in src.C]
    def enc(v):
        return [str(m.exact_binary_rational(t)) for t in v._mpi_]
    def display(v):
        return [m.mp.nstr(x, 90) for x in m.endpoints(v)]
    separated = [i for i, v in enumerate(residual) if m.endpoints(v.v)[1] < 0 or m.endpoints(v.v)[0] > 0]
    negative = m.endpoints(diagonal.v)[1] < 0 and m.endpoints(score.v)[1] < 0
    result = {
        "status": "EXECUTED_OUTWARD_FULL_CAP6_RESPONSE_OF_VALIDATED_NEARBY_CAP5_CUBE",
        "original_source_sha256": original_sha, "helper_sha256": HELPER_SHA,
        "executed_interval_provider_sha256": PROVIDER_SHA, "executed_full6_source_extension_sha256": FULL6_SHA,
        "input_sha256": input_sha, "cap5_certificate_sha256": sha256(cert_raw).hexdigest(),
        "own_source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "parameter_cube_radius": str(radius), "parameter_order": doc["parameter_order"],
        "mpmath_version": m.mp.__version__, "outward_precision_digits": 160,
        "source_family": "Same original fair independent CURRENT-root eight-cell chart; exact rational means/w4/U/seam; same parameters in both copies and every arity",
        "pair_target": "1/4", "candidate_not_claimed_exact_centre": True,
        "unknown_cap5_root_enclosed": "Every reported cube interval encloses the implicit exact root if this new contraction certificate/source application is independently accepted",
        "new_cap5_certificate_independent_review_pending": True,
        "exact_source_controls": src.source_controls,
        "full20_cube_row_intervals": [enc(v.v) for v in row],
        "full20_cube_residual_intervals": [enc(v.v) for v in residual],
        "full20_cube_residual_decimal_displays": [display(v.v) for v in residual],
        "lower_cap5_deletion_residual_cube_intervals": [enc(v.v) for v in lower],
        "lower_cap5_residual_at_implicit_root_zero_if_certificate_accepted": True,
        "cap6_free_indices": h.FREE,
        "cap6_nine_free_residual_intervals": [enc(residual[i].v) for i in h.FREE],
        "tight_b6_minus_d15_interval": enc(diagonal.v),
        "tight_b6_minus_d15_decimal_display": display(diagonal.v),
        "tight_Delta6_interval": enc(score.v),
        "tight_Delta6_decimal_display": display(score.v),
        "negative_new_diagonal_over_entire_cube": negative,
        "full20_response_separating_indices_over_entire_cube": separated,
        "direct_row_vs_telescoped_diagonal_interval_contains_zero": True,
        "all_original_source_parameters_strict_over_entire_cube": physical,
        "ordinary_edge_survival_intervals": [enc(v.v) for v in edges],
        "arm_inequality_intervals": [[enc(v) for v in gates] for gates in arms],
        "interval_endpoint_encoding": "Exact rational representations of outward binary endpoints; decimal values are displays",
        "runtime_seconds": time.perf_counter()-started,
        "not_claimed": ["independent acceptance of new roots by this author", "opposite Delta6", "cap-six common zero", "new diagonal equality", "all-cap source theorem", "G4 closure"]}
    args.output.write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps({"status": result["status"], "output": str(args.output), "Delta6": result["tight_Delta6_decimal_display"],
                      "negative_over_entire_cube": negative, "runtime_seconds": result["runtime_seconds"]}))


if __name__ == "__main__":
    main()
