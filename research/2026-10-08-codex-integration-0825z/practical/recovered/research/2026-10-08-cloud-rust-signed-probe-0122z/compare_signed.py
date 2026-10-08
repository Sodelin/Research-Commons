"""Post-gate bounded differential against verified Python bytes; not yet run.

No source-forward evaluator or observations are executed. The only archived
fields used are already saved mean enclosures and physical point boxes.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
from types import ModuleType

FEATURES = ("AC1", "AC2", "CC1", "BC1", "BC2", "AB1", "AB2", "AA1", "BB1")
PHYSICAL = ("h", "u", "v", "rA", "rB", "rC", "rAB", "rR", "g")
RESIDUALS = ("root", "root_time", "h", "g", "AB1", "AB2", "BB1")
REFERENCE = "research/2026-10-07-cloud-practical-signed-guard-2159z/signed_receiver.py"
REFERENCE_SHA = "61db9997db84b925c6eff405744726e01dcec14d0090192e834f33a75aeafc1f"
PROVIDER = "research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py"
PROVIDER_SHA = "c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace"
ARCHIVE = "research/2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json"
ARCHIVE_SHA = "8acf47eadbb01e220f9ebb87746b64f070a0f527bfc0a230e58b316e9f3c6931"


def authenticated(path, digest):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != digest:
        raise RuntimeError("source identity mismatch: " + str(path))
    return data


def load_reference(root):
    data = authenticated(root / REFERENCE, REFERENCE_SHA)
    authenticated(root / PROVIDER, PROVIDER_SHA)
    module = ModuleType("_cloud_signed_probe_verified_reference")
    module.__file__ = str(root / REFERENCE)
    sys.modules[module.__name__] = module
    exec(compile(data, module.__file__, "exec", dont_inherit=True), module.__dict__)
    return module


def fixture_cases(saved):
    means, points = saved["source_forward_mean_boxes"], saved["source_parameter_points"]
    cases = []

    def add(identifier, m0=None, m1=None, p0=None, p1=None, precision=96, bits=4096, cap=24):
        cases.append({"id": identifier, "means0": copy.deepcopy(means[0] if m0 is None else m0),
                      "means1": copy.deepcopy(means[0] if m1 is None else m1),
                      "physical0": copy.deepcopy(p0), "physical1": copy.deepcopy(p1),
                      "precision": precision, "max_bits": bits, "max_exp_calls": cap})

    hull = {k: [str(min(Fraction(means[0][k][0]), Fraction(means[1][k][0]))),
                str(max(Fraction(means[0][k][1]), Fraction(means[1][k][1])))] for k in FEATURES}
    add("archived_common")
    add("archived_second_common", means[1], means[1])
    add("archived_pair", means[0], means[1])
    add("archived_reverse_pair", means[1], means[0])
    add("archived_hull", hull, hull)
    add("archived_point_pair", means[0], means[1], points[0], points[1])
    add("archived_reverse_points", means[1], means[0], points[1], points[0])
    for identifier, rate_hi in (("supplied_box_width_below", "5/4"), ("supplied_box_width_above", "21/16")):
        physical = copy.deepcopy(points[0]); physical["rA"] = ["1", rate_hi]
        add(identifier, hull, hull, physical, physical)
    for precision in (64, 128):
        add("precision_" + str(precision), precision=precision)
    for cap in range(9):
        add("exp_cap_" + str(cap), cap=cap)
    add("bit_budget_256", bits=256)
    add("precision_128_bits_256", precision=128, bits=256)
    add("precision_refusal", precision=63)
    add("bit_config_refusal", bits=255)
    add("exp_config_refusal", cap=33)
    changed = copy.deepcopy(means[0]); changed["AC1"] = ["1/2", "1/2"]
    add("root_zero", changed, changed)
    changed = copy.deepcopy(means[0]); changed["AC1"] = ["0", "1/4"]
    add("empty_mean_intersection", changed, changed)
    changed = copy.deepcopy(means[0]); changed["BC1"] = changed["AC1"]
    add("pulse_zero", changed, changed)
    changed = copy.deepcopy(means[0]); changed["BC1"] = ["1/2", "1/2"]
    add("pulse_negative", changed, changed)
    for identifier, endpoint in (("zero_denominator", "1/0"), ("raw_bits", str(1 << 256)),
                                 ("raw_grammar", "1e-1000000000"), ("raw_length", "9" * 159),
                                 ("raw_digit_limit", "9" * 79), ("decimal_unsupported", "0.75"),
                                 ("negative_mean", "-1/4")):
        changed = copy.deepcopy(means[0]); changed["AC1"][0] = endpoint
        add(identifier, changed)
    changed = copy.deepcopy(means[0]); changed["AC1"] = ["3/4", "1/2"]
    add("reversed_mean_interval", changed)
    physical = copy.deepcopy(points[0]); physical["h"] = ["0", "1/16"]
    add("physical_domain", p0=physical, p1=points[0])
    physical = copy.deepcopy(points[0]); physical["g"] = ["1/3", "1/4"]
    add("physical_reversed", p0=physical, p1=points[0])
    return cases


def row(case):
    boxes = case["physical0"] is not None
    if boxes != (case["physical1"] is not None):
        raise RuntimeError("probe requires both optional physical boxes")
    fields = ["pair", case["id"], str(case["precision"]), str(case["max_bits"]),
              str(case["max_exp_calls"]), "boxes" if boxes else "default"]
    for name, keys in (("means0", FEATURES), ("means1", FEATURES)):
        fields.extend(endpoint for key in keys for endpoint in case[name][key])
    if boxes:
        for name in ("physical0", "physical1"):
            fields.extend(endpoint for key in PHYSICAL for endpoint in case[name][key])
    return "\t".join(fields)


def project_reference(result):
    projection = {key: result[key] for key in ("status", "scalar_exp_calls", "precision_fractional_bits", "arithmetic_max_bits")}
    projection["refusal"] = result.get("refusal")
    for key in ("difference_intervals", "normalized_absolute_difference_bounds",
                "maximum_normalized_difference_bound", "signed_residuals"):
        if key in result:
            projection[key] = result[key]
    return projection


def parse_native(line, case):
    fields = line.split("\t")
    if len(fields) not in (16, 58) or fields[:2] != ["result", case["id"]]:
        raise RuntimeError("invalid native response shape")
    if fields[7:10] != [str(case["max_exp_calls"]), PROVIDER_SHA, "native_exact_interval_core"] or fields[10:16] != ["0"] * 6:
        raise RuntimeError("native metadata or scientific flags changed")
    result = {"status": fields[2], "refusal": None if fields[3] == "-" else fields[3],
              "scalar_exp_calls": int(fields[4]), "precision_fractional_bits": int(fields[5]),
              "arithmetic_max_bits": int(fields[6])}
    if len(fields) == 58:
        result["difference_intervals"] = {key: fields[16+2*i:18+2*i] for i, key in enumerate(PHYSICAL)}
        result["normalized_absolute_difference_bounds"] = dict(zip(PHYSICAL, fields[34:43]))
        result["maximum_normalized_difference_bound"] = fields[43]
        result["signed_residuals"] = {key: fields[44+2*i:46+2*i] for i, key in enumerate(RESIDUALS)}
    return result


def child_limits():
    resource.setrlimit(resource.RLIMIT_CPU, (15, 15))
    resource.setrlimit(resource.RLIMIT_AS, (256 * 2**20, 256 * 2**20))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run_native(binary, data, destination, name):
    command = [str(binary)]
    started = time.time()
    try:
        completed = subprocess.run(command, input=data, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   timeout=30, preexec_fn=child_limits, check=False)
        code, stdout, stderr = completed.returncode, completed.stdout, completed.stderr
        outcome = "TERMINAL"
    except subprocess.TimeoutExpired as error:
        code, stdout, stderr = None, error.stdout or b"", error.stderr or b""
        outcome = "TIMEOUT"
    (destination / (name + ".stdin")).write_bytes(data)
    (destination / (name + ".stdout")).write_bytes(stdout)
    (destination / (name + ".stderr")).write_bytes(stderr)
    receipt = {"command": command, "started_unix": started, "ended_unix": time.time(),
               "exit_code": code, "state": outcome, "stdout_bytes": len(stdout), "stderr_bytes": len(stderr),
               "cpu_seconds": 15, "wall_seconds": 30, "address_space_bytes": 256 * 2**20}
    (destination / (name + ".execution.json")).write_text(json.dumps(receipt, indent=2) + "\n")
    if code != 0 or stderr or len(stdout) > 4 * 2**20:
        raise RuntimeError("native process failed or exceeded declared output guard")
    return stdout.decode("ascii").splitlines()


def source_state(root, manifest):
    result = {}
    for path, identity in manifest["files"].items():
        data = authenticated(root / path, identity["sha256"])
        if len(data) != identity["bytes"]:
            raise RuntimeError("source length mismatch")
        result[path] = identity
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("binary", type=Path)
    parser.add_argument("destination", type=Path)
    args = parser.parse_args()
    root, binary, destination = args.root.resolve(), args.binary.resolve(), args.destination.resolve()
    destination.mkdir(parents=True, exist_ok=False)
    packet = Path(__file__).resolve().parent
    manifest = json.loads((packet / "FROZEN-SOURCES.json").read_bytes())
    before = source_state(root, manifest)
    binary_sha = hashlib.sha256(binary.read_bytes()).hexdigest()
    (destination / "BEFORE.json").write_text(json.dumps({"sources": before, "binary_sha256": binary_sha}, indent=2) + "\n")
    started = time.time()
    report = {"status": "UNKNOWN", "new_source_forward_evaluations": 0, "observation_rows_replayed": 0,
              "data_confidence_certificate_issued": False, "outer_cover_validated": False,
              "mean_band_coverage_admitted": False, "compatible_source_existence_verified": False,
              "literal_archived_means_sha256": ARCHIVE_SHA, "cases": []}
    try:
        reference = load_reference(root)
        saved = json.loads(authenticated(root / ARCHIVE, ARCHIVE_SHA))
        cases = fixture_cases(saved)
        if len(cases) > 96:
            raise RuntimeError("fixture count exceeds probe cap")
        (destination / "CASES.json").write_text(json.dumps(cases, indent=2) + "\n")
        expected = []
        for case in cases:
            result = reference.receive(root, case["means0"], case["means1"], case["physical0"], case["physical1"],
                                       case["precision"], case["max_bits"], case["max_exp_calls"])
            if result["data_confidence_certificate_issued"] or result["outer_cover_validated"]:
                raise RuntimeError("reference scientific flags changed")
            expected.append(result)
        (destination / "PYTHON-EXPECTED.json").write_text(json.dumps(expected, indent=2) + "\n")
        lines = run_native(binary, ("\n".join(map(row, cases)) + "\n").encode("ascii"), destination, "geometry")
        if len(lines) != len(cases):
            raise RuntimeError("native row count differs")
        for case, python, native_line in zip(cases, expected, lines):
            native, projected = parse_native(native_line, case), project_reference(python)
            report["cases"].append({"id": case["id"], "matches": native == projected,
                                    "native": native, "python_projection": projected})
        by_id = {case["id"]: result for case, result in zip(cases, expected)}
        if by_id["archived_common"]["status"] != "CONDITIONAL_PAIR_WIDTH_CERTIFIED" or by_id["archived_pair"]["status"] != "UNKNOWN":
            raise RuntimeError("archived controlling geometry differs")
        guards = [(b"not-a-request\n", "protocol\t-\tPROBE_SHAPE"),
                  (b"x" * 32769 + b"\n", "protocol\t-\tPROBE_LINE"),
                  (b"pair\t" + b"x" * 4097 + b"\n", "protocol\t-\tPROBE_FIELD"),
                  (b"pair\t\xff\n", "protocol\t-\tPROBE_ASCII"),
                  (b"pair\r\n", "protocol\t-\tPROBE_ASCII"),
                  (b"pair\tid\t96\t4096\t24\tother\n", "protocol\tid\tPROBE_MODE"),
                  (b"pair\t!\t96\t4096\t24\tdefault\n", "protocol\t-\tPROBE_ID")]
        bad_integer = row(cases[0]).replace("\t96\t", "\t2147483648\t", 1).encode() + b"\n"
        guards.append((bad_integer, "protocol\tarchived_common\tPROBE_INTEGER"))
        guards.append((b"unterminated", "protocol\t-\tPROBE_FRAME"))
        protocol_lines = run_native(binary, b"".join(item[0] for item in guards), destination, "protocol")
        protocol_expected = [item[1] for item in guards]
        rows_lines = run_native(binary, b"bad\n" * 97, destination, "row_limit")
        rows_expected = ["protocol\t-\tPROBE_SHAPE"] * 96 + ["protocol\t-\tPROBE_ROWS"]
        report["protocol_controls"] = {"matches": protocol_lines == protocol_expected, "expected": protocol_expected, "actual": protocol_lines}
        report["row_limit_control"] = {"matches": rows_lines == rows_expected, "response_count": len(rows_lines)}
        report["exact_geometry_cases"] = len(cases)
        report["geometry_differences"] = sum(not item["matches"] for item in report["cases"])
        report["completed_geometry_cases"] = sum("difference_intervals" in item for item in expected)
        report["reference_refusal_cases"] = sum("refusal" in item for item in expected)
        if report["geometry_differences"] or not report["protocol_controls"]["matches"] or not report["row_limit_control"]["matches"]:
            raise RuntimeError("differential or transport control mismatch")
        report["status"] = "PASS"
    except Exception as error:
        report["failure"] = {"type": type(error).__name__, "message": str(error)}
    finally:
        try:
            after = source_state(root, manifest)
        except Exception as error:
            after = {"identity_failure": {"type": type(error).__name__, "message": str(error)}}
        after_binary = hashlib.sha256(binary.read_bytes()).hexdigest()
        unchanged = before == after and binary_sha == after_binary
        report.update(started_unix=started, ended_unix=time.time(), source_and_binary_unchanged=unchanged,
                      binary_sha256=binary_sha, python_version=sys.version,
                      python_provider_execution="compile_exec_verified_single_read_bytes",
                      native_provider_execution="native_exact_interval_core")
        if not unchanged:
            report["status"] = "UNKNOWN"
            report["failure"] = {"type": "SourceIdentity", "message": "source or binary changed during run"}
        (destination / "AFTER.json").write_text(json.dumps({"sources": after, "binary_sha256": after_binary}, indent=2) + "\n")
        (destination / "RESULT.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report.get(key) for key in ("status", "exact_geometry_cases", "geometry_differences", "failure", "source_and_binary_unchanged")}))
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
