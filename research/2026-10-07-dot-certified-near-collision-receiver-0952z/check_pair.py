"""Independent rational closed-form check; imports no forward/producer module."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
import re

BASE = Path(__file__).resolve().parent
FEATURES = ("AC1", "AC2", "CC1", "BC1", "BC2", "AB1", "AB2", "AA1", "BB1")
PHYSICAL = ("h", "u", "v", "rA", "rB", "rC", "rAB", "rR", "g")
PROVIDER_SHA = "c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace"


def require(value, message):
    if not value:
        raise ValueError(message)


def rational(value):
    require(isinstance(value, str) and re.fullmatch(r"-?\d+(?:/[1-9]\d*)?", value), "exact rational string")
    return Q(value)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def interval(value):
    require(isinstance(value, list) and len(value) == 2, "two endpoints")
    lo, hi = map(rational, value)
    require(lo <= hi, "ordered interval")
    return lo, hi


def main():
    input_path = BASE / "SOURCE-INPUT.json"
    result_path = BASE / "attempt1" / "scientific" / "PAIR-FORWARD.json"
    request = json.loads(input_path.read_text())
    result = json.loads(result_path.read_text())
    original = {k: ["1/32", "1/8"] if k in ("h", "u", "v") else
                ["1/6", "2/3"] if k == "g" else ["1/2", "6"] for k in PHYSICAL}
    first = dict(h="1/32", u="1/32", v="1/32", rA="57/10", rB="6", rC="6", rAB="6", rR="6", g="1/4")
    second = {**first, "rA": "6"}
    require(request["domain"] == original and request["sources"] == [first, second], "exact proposed sources/domain")
    require(tuple(request["features"]) == tuple(result["features"]) == FEATURES, "whole nine-feature vector")
    require(request["model"] == result["model"] == "fixed-six-copy-clock-jc-nine-v1"
            and request["quantity"] == result["quantity"] == "shifted_bernoulli_character_mean", "model/units")
    require(result["schema"] == "certified_fixed_jc_pair_forward_v1"
            and result["status"] == "FORWARD_ENCLOSURES_PRODUCED", "producer result schema")
    require(result["input_sha256"] == digest(input_path) and result["provider_sha256"] == PROVIDER_SHA,
            "scientific input/provider identities")
    require(result["pair_expression_calls"] == 4 and result["exponential_precision_bits"] == 128,
            "declared arithmetic scope")
    require(result["new_observations_acquired"] is False and result["inverse_invoked"] is False
            and result["statistical_admission_claimed"] is False, "scientific release scope")
    require(len(result["sources"]) == 2, "exactly two sources")
    means = []
    for physical, record in zip(request["sources"], result["sources"]):
        require(record["physical_parameters"] == physical, "whole source vector identity")
        p = {k: rational(v) for k, v in physical.items()}
        for key in PHYSICAL:
            lo, hi = map(rational, original[key])
            require(lo <= p[key] <= hi, "strict original mathematical domain")
        expected = {k: str(p[k]) for k in ("h", "g", "rA", "rB", "rC", "rAB", "rR")}
        expected.update(t1=str(p["h"]+p["u"]), t0=str(p["h"]+p["u"]+p["v"]))
        require(record["forward_parameters"] == expected, "shared time/rate parameterization")
        row = record["shifted_mean_enclosures"]
        require(set(row) == set(FEATURES), "complete features")
        row = {key: interval(value) for key, value in row.items()}
        require(all(0 <= lo <= hi <= 1 and hi-lo <= Q(1, 2**100) for lo, hi in row.values()), "enclosure range/width")
        means.append(row)
    gaps = {}
    require(set(result["coordinate_difference_enclosures"]) == set(FEATURES), "all coordinate differences")
    for key in FEATURES:
        a, b = means[0][key]
        c, d = means[1][key]
        gaps[key] = (c-b, d-a)
        require(interval(result["coordinate_difference_enclosures"][key]) == gaps[key], "difference arithmetic")
        if key != "AA1":
            require(means[0][key] == means[1][key], "eight common enclosure records")
    joint = (max(max(Q(0), lo, -hi) for lo, hi in gaps.values()),
             max(max(abs(lo), abs(hi)) for lo, hi in gaps.values()))
    require(interval(result["joint_sup_gap_enclosure"]) == joint
            and joint == gaps["AA1"] and 0 < joint[0] <= joint[1] < Q(1, 400), "complete joint gap")
    separations = {k: abs(rational(second[k])-rational(first[k])) /
                  (rational(original[k][1])-rational(original[k][0])) for k in PHYSICAL}
    require(result["normalized_coordinate_separations"] == {k: str(v) for k, v in separations.items()}
            and max(separations.values()) == rational(result["normalized_sup_separation"]) == Q(3, 55)
            and Q(3, 55) > Q(1, 20), "whole-domain physical separation")
    x = Q(251, 480)
    term = partial = Q(1)
    s20 = None
    for degree in range(1, 22):
        previous = abs(term)
        term *= -x / degree
        require(abs(term) < previous, "alternating term decrease")
        partial += term
        if degree == 20:
            s20 = partial
    s21 = partial
    require(0 < s21 < s20 < 1, "fixed exponential Taylor enclosure")
    closed = (Q(18, 3263)*(1-s20), Q(18, 3263)*(1-s21))
    require(closed[0] <= joint[0] <= joint[1] <= closed[1] < Q(1, 400), "independent closed-form gap check")
    require(means[1]["AA1"][0] <= Q(11, 13) <= means[1]["AA1"][1], "exact homogeneous AA mean")
    require(Q(11, 13)-closed[1] <= means[0]["AA1"][0]
            <= means[0]["AA1"][1] <= Q(11, 13)-closed[0], "lower-source AA closed-form check")
    require(Q(18, 9503) <= closed[0] and closed[1] <= Q(36, 15743) < Q(1, 400), "rational analytic bracket")
    output = {"schema": "independent_fixed_jc_pair_check_v1", "status": "PASS_TWO_SOURCE_ENCLOSURE_ONLY",
              "input_sha256": digest(input_path), "forward_output_sha256": digest(result_path),
              "series_terms": 22, "exponential_argument": "251/480",
              "independent_exp_enclosure": [str(s21), str(s20)],
              "independent_gap_enclosure": [str(v) for v in closed],
              "joint_forward_gap_enclosure": [str(v) for v in joint],
              "normalized_sup_separation": "3/55", "joint_gap_upper_target_met": True,
              "other_eight_mean_records_equal": True,
              "mathematical_equalities_rely_on_reviewed_source_formula": True,
              "provider_imported_by_checker": False, "producer_imported_by_checker": False,
              "new_observations_acquired": False, "inverse_localization_claimed": False,
              "uniform_lower_delta_claimed_by_this_check": False}
    with (result_path.parent / "CLOSED-FORM-CHECK.json").open("x") as stream:
        json.dump(output, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": output["status"], "series_terms": 22,
                      "normalized_sup_separation": "3/55", "joint_gap_below": "1/400"}))


if __name__ == "__main__":
    main()
