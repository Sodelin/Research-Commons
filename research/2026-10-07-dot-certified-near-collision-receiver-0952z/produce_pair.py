"""Two exact source vectors through the unchanged published forward provider."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

BASE = Path(__file__).resolve().parent
PROVIDER_SHA = "c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace"
FEATURES = ("AC1", "AC2", "CC1", "BC1", "BC2", "AB1", "AB2", "AA1", "BB1")
PHYSICAL = ("h", "u", "v", "rA", "rB", "rC", "rAB", "rR", "g")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    source = BASE / "certified_forward.py"
    require(not source.is_symlink() and sha(source) == PROVIDER_SHA, "forward source identity")
    request_path = BASE / "SOURCE-INPUT.json"
    request = json.loads(request_path.read_text())
    require(request["schema"] == "fixed-jc-rational-source-pair-v1"
            and request["model"] == "fixed-six-copy-clock-jc-nine-v1"
            and request["quantity"] == "shifted_bernoulli_character_mean", "fixed source contract")
    require(tuple(request["features"]) == FEATURES and len(request["sources"]) == 2,
            "exact two-source nine-feature scope")
    require(request["exponential_precision_bits"] == 128
            and Q(request["maximum_mean_width"]) == Q(1, 2**100), "fixed precision")
    spec = importlib.util.spec_from_file_location("_pair_certified_forward", source)
    forward = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = forward
    spec.loader.exec_module(forward)
    results = []
    for physical in request["sources"]:
        require(set(physical) == set(PHYSICAL), "all physical parameters shared")
        values = {k: forward.rational(v) for k, v in physical.items()}
        for k in PHYSICAL:
            lo, hi = map(Q, request["domain"][k])
            require(lo <= values[k] <= hi, "original domain")
        p = {k: values[k] for k in ("h", "g", "rA", "rB", "rC", "rAB", "rR")}
        p.update(t1=values["h"] + values["u"], t0=values["h"] + values["u"] + values["v"])
        p = forward.validate(p)
        by_k = {k: forward.pair_expressions(p, Q(8*k, 3), lambda x: forward.exp_neg(x, 128))
                for k in (1, 2)}
        means = {}
        for feature in FEATURES:
            value = (1 + by_k[int(feature[-1])][feature[:2]]) / 2
            require(0 <= value.lo <= value.hi <= 1, "mean enclosure range")
            require(value.width <= Q(1, 2**100), "mean enclosure too wide")
            means[feature] = [str(value.lo), str(value.hi)]
        results.append({"physical_parameters": physical,
                        "forward_parameters": {k: str(v) for k, v in p.items()},
                        "shifted_mean_enclosures": means})
    differences = {}
    for feature in FEATURES:
        a, b = [Q(v) for v in results[0]["shifted_mean_enclosures"][feature]]
        c, d = [Q(v) for v in results[1]["shifted_mean_enclosures"][feature]]
        differences[feature] = [str(c-b), str(d-a)]
    lower = max(max(Q(0), Q(lo), -Q(hi)) for lo, hi in differences.values())
    upper = max(max(abs(Q(lo)), abs(Q(hi))) for lo, hi in differences.values())
    widths = {k: abs(Q(request["sources"][1][k])-Q(request["sources"][0][k])) /
              (Q(request["domain"][k][1])-Q(request["domain"][k][0])) for k in PHYSICAL}
    require(max(widths.values()) == Q(3, 55) and upper < Q(1, 400) and lower > 0,
            "expected strict separation bounds")
    require(all(results[0]["shifted_mean_enclosures"][k] == results[1]["shifted_mean_enclosures"][k]
                for k in FEATURES if k != "AA1"), "unchanged eight mean records")
    require(sha(source) == PROVIDER_SHA, "forward source changed after use")
    output = {"schema": "certified_fixed_jc_pair_forward_v1", "status": "FORWARD_ENCLOSURES_PRODUCED",
              "input_sha256": sha(request_path), "provider_sha256": PROVIDER_SHA,
              "model": request["model"], "quantity": request["quantity"], "features": list(FEATURES),
              "exponential_precision_bits": 128, "pair_expression_calls": 4,
              "maximum_mean_width": request["maximum_mean_width"], "sources": results,
              "coordinate_difference_enclosures": differences,
              "joint_sup_gap_enclosure": [str(lower), str(upper)],
              "normalized_coordinate_separations": {k: str(v) for k, v in widths.items()},
              "normalized_sup_separation": "3/55", "new_observations_acquired": False,
              "inverse_invoked": False, "statistical_admission_claimed": False}
    out = BASE / "attempt1" / "scientific"
    out.mkdir(exist_ok=False)
    with (out / "PAIR-FORWARD.json").open("x") as stream:
        json.dump(output, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": output["status"], "sources": 2, "features_per_source": 9,
                      "pair_expression_calls": 4}))


if __name__ == "__main__":
    main()
