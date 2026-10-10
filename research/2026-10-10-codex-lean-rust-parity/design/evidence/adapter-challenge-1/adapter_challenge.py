#!/usr/bin/env python3
"""Independent bounded challenges for the optional native affine adapter.

Uses actual subprocess starts and original-row certificates. Forged producers
are intentional test fixtures, not sources or scientific counterexamples.
Historical provider bytes and shared production files are never modified.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from types import ModuleType

from certificate_check import verify_certificate, require

DESIGN = Path(__file__).resolve().parent
PACKET = DESIGN.parent
ROOT = PACKET.parents[1]
ADAPTER = PACKET / "rust/native_component.py"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load_adapter(name):
    module = ModuleType(name)
    module.__file__ = str(ADAPTER)
    sys.modules[name] = module
    raw = ADAPTER.read_bytes()
    exec(compile(raw, str(ADAPTER), "exec"), module.__dict__)
    return module, raw


def forged_producer(path, certificate, exit_code=0, checker_accept=True):
    # Repr produces literals, not shell substitutions. The staged executable
    # uses the system Python under the adapter's minimal child environment.
    checker_bytes = b"RC1 CHECK ACCEPT\n" if checker_accept else b"RC1 CHECK REJECT\n"
    source = ("#!/usr/bin/python3\nimport sys\n"
              "if len(sys.argv) > 1 and sys.argv[1] == 'check':\n"
              f"    sys.stdout.buffer.write({checker_bytes!r})\n"
              f"    sys.exit({0 if checker_accept else 1})\n"
              f"sys.stdout.buffer.write({certificate!r})\n"
              f"sys.exit({exit_code})\n")
    path.write_text(source)
    path.chmod(0o700)
    return path


def envelope(request, body):
    return b"RC1 RESULT AFFINE\nBEGIN_REQUEST\n" + request + b"END_REQUEST\n" + body + b"END\n"


def run(args):
    output = args.output.resolve()
    require(not output.exists(), "challenge output already exists")
    output.mkdir(parents=True)
    fixtures = output / "challenge-inputs"
    fixtures.mkdir()
    binary = args.binary.resolve()
    require(binary.is_file(), "native executable is absent")
    binary_sha = sha(binary.read_bytes())
    module, adapter_raw = load_adapter("independent_native_adapter_challenge")
    (output / "native_component.py").write_bytes(adapter_raw)
    helper_raw = (DESIGN / "certificate_check.py").read_bytes()
    (output / "certificate_check.py").write_bytes(helper_raw)

    sat_request = b"RC1 AFFINE 1 1 4096\nLE 1/1 1/1\n"
    unsat_request = b"RC1 AFFINE 1 2 4096\nLT 1/1 1/1\nLE -1/1 -1/1\n"
    unknown_request = b"RC1 AFFINE 1 2 0\nLE 1/1 1/1\nLE 0/1 -1/1\n"
    sat = fixtures / "sat.req"
    unsat = fixtures / "unsat.req"
    unknown = fixtures / "unknown.req"
    sat.write_bytes(sat_request)
    unsat.write_bytes(unsat_request)
    unknown.write_bytes(unknown_request)
    valid_sat = envelope(sat_request, b"STATUS SAT\nWITNESS 1 0/1\nEVAL 1 0/1\n")
    valid_unsat = envelope(unsat_request,
                          b"STATUS UNSAT\nMULTIPLIERS 2 1/1 1/1\nBOUND 0/1\nSTRICT 1\n")
    valid_unknown = envelope(unknown_request, b"STATUS UNKNOWN\nLIMIT 1 1 0\n")
    verify_certificate(sat_request, valid_sat, 0)
    verify_certificate(unsat_request, valid_unsat, 0)
    verify_certificate(unknown_request, valid_unknown, 2)
    records = []

    def check(name, request, producer, status, *, pin=None, solver=None,
              native_checker=None, fraction_checker=None, instance=module):
        destination = output / name
        start = time.monotonic()
        result = instance.execute(request, destination, producer, pin)
        errors = []
        if result["status"] != status:
            errors.append(f"status {result['status']} != {status}")
        for field, expected in (("solver_called", solver), ("checker_called", native_checker),
                                ("fraction_checker_called", fraction_checker)):
            if expected is not None and result[field] is not expected:
                errors.append(f"{field} {result[field]} != {expected}")
        if result.get("source_admission_verified") is not False or result.get("source_witness_certified") is not False:
            errors.append("affine result promoted scientific source admission")
        if result.get("unrestricted_exclusion_certified") is not False:
            errors.append("matrix exclusion promoted unrestricted source exclusion")
        if status in ("MATRIX_WITNESS", "MATRIX_EXCLUSION"):
            require(result["certificate_checked"], "matrix answer omitted independent checking")
            checked = verify_certificate((destination / "REQUEST.rc1").read_bytes(),
                                         (destination / "CERTIFICATE.rc1").read_bytes(), 0)
            require(checked["certificate_valid"], "accepted matrix answer has no original-row certificate")
        record = {"case": name, "pass": not errors, "errors": errors,
                  "elapsed_seconds": time.monotonic() - start,
                  "expected": status, "observed": result["status"],
                  "result": str((destination / "RESULT.json").relative_to(output))}
        records.append(record)
        return destination

    check("actual_witness", sat, binary, "MATRIX_WITNESS", pin=binary_sha,
          solver=True, native_checker=True, fraction_checker=True)
    check("actual_exclusion", unsat, binary, "MATRIX_EXCLUSION", pin=binary_sha,
          solver=True, native_checker=True, fraction_checker=True)
    check("actual_projection_unknown", unknown, binary, "UNKNOWN", pin=binary_sha,
          solver=True, native_checker=False, fraction_checker=False)
    check("expected_binary_mismatch", sat, binary, "REFUSED_REQUEST", pin="0" * 64,
          solver=False, native_checker=False, fraction_checker=False)
    invalid_exec = fixtures / "not-an-executable"
    invalid_exec.write_bytes(b"this is not an executable\n")
    check("before_start_exec_failure", sat, invalid_exec, "RESOURCE_OR_EXECUTION_FAILURE",
          solver=False, native_checker=False, fraction_checker=False)
    crash = forged_producer(fixtures / "after-start-crash", b"", 5)
    check("after_start_crash", sat, crash, "RESOURCE_OR_EXECUTION_FAILURE",
          solver=True, native_checker=False, fraction_checker=False)
    wrong_exit = forged_producer(fixtures / "wrong-exit-sat", valid_sat, 2)
    check("sat_status_exit_mismatch", sat, wrong_exit, "REFUSED_REQUEST",
          solver=True, native_checker=False, fraction_checker=False)
    unknown_exit = forged_producer(fixtures / "wrong-exit-unknown", valid_unknown, 0)
    check("unknown_status_exit_mismatch", unknown, unknown_exit, "REFUSED_REQUEST",
          solver=True, native_checker=False, fraction_checker=False)
    wrong_echo = forged_producer(fixtures / "changed-request-echo", valid_unsat)
    check("request_substitution", sat, wrong_echo, "REFUSED_REQUEST",
          solver=True, native_checker=False, fraction_checker=False)
    bad_witness = forged_producer(fixtures / "forged-witness", envelope(sat_request,
                       b"STATUS SAT\nWITNESS 1 2/1\nEVAL 1 2/1\n"))
    check("forged_witness_native_accepts", sat, bad_witness, "REFUSED_REQUEST",
          solver=True, native_checker=True, fraction_checker=True)
    bad_strict = forged_producer(fixtures / "forged-strictness", valid_unsat.replace(b"STRICT 1", b"STRICT 0"))
    check("forged_strictness_native_accepts", unsat, bad_strict, "REFUSED_REQUEST",
          solver=True, native_checker=True, fraction_checker=True)
    malformed_certificate = forged_producer(fixtures / "truncated-certificate", valid_sat[:-4])
    check("truncated_certificate", sat, malformed_certificate, "REFUSED_REQUEST",
          solver=True, native_checker=True, fraction_checker=True)

    # Hash-drift controls execute an isolated module instance. They change only
    # owned challenge fixtures, never a historical or production provider.
    helper_instance, _ = load_adapter("independent_helper_drift_challenge")
    changed_helper = fixtures / "changed-certificate-check.py"
    changed_helper.write_bytes(helper_raw + b"\n# deliberate identity drift fixture\n")
    helper_instance.FRACTION_HELPER = changed_helper
    check("fraction_helper_hash_drift", sat, binary, "REFUSED_REQUEST", solver=False,
          native_checker=False, fraction_checker=False, instance=helper_instance)
    source_instance, _ = load_adapter("independent_source_drift_challenge")
    source_fixture = fixtures / "changed-owned-source.rs"
    source_fixture.write_bytes(b"deliberately different challenge source\n")
    source_fixture_path = str(source_fixture.relative_to(ROOT))
    altered_manifest_dir = fixtures / "source-manifest"
    altered_manifest_dir.mkdir()
    (altered_manifest_dir / "INHERITED-SOURCES.json").write_text(json.dumps({"files": [
        {"path": source_fixture_path, "sha256": sha(b"expected original challenge source\n")}
    ]}) + "\n")
    source_instance.HERE = altered_manifest_dir
    check("source_hash_drift", sat, binary, "REFUSED_REQUEST", solver=False,
          native_checker=False, fraction_checker=False, instance=source_instance)

    existing = output / "actual_witness"
    before = sha((existing / "RESULT.json").read_bytes())
    refused = False
    try:
        module.execute(sat, existing, binary, binary_sha)
    except FileExistsError:
        refused = True
    after = sha((existing / "RESULT.json").read_bytes())
    records.append({"case": "fresh_output_no_overwrite", "pass": refused and before == after,
                    "errors": [] if refused and before == after else ["existing evidence changed/not refused"],
                    "result_before_sha256": before, "result_after_sha256": after})
    stable_binary = sha(binary.read_bytes()) == binary_sha
    stable_adapter = ADAPTER.read_bytes() == adapter_raw
    stable_helper = (DESIGN / "certificate_check.py").read_bytes() == helper_raw
    receipt = {"claim": "INDEPENDENT_BOUNDED_NATIVE_ADAPTER_CHALLENGES",
               "source_admission_claim": False, "universal_correspondence_claim": False,
               "executed_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
               "cases_total": len(records), "cases_passed": sum(r["pass"] for r in records),
               "pass": all(r["pass"] for r in records) and stable_binary and stable_adapter and stable_helper,
               "identities": {"binary": {"path": str(binary), "sha256": binary_sha, "stable": stable_binary},
                              "adapter": {"path": str(ADAPTER), "sha256": sha(adapter_raw), "stable": stable_adapter},
                              "fraction_checker": {"sha256": sha(helper_raw), "stable": stable_helper},
                              "challenge_harness": {"sha256": sha(Path(__file__).read_bytes())}},
               "cases": records}
    (output / "ADAPTER-CHALLENGE-RECEIPT.json").write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"pass": receipt["pass"], "cases_passed": receipt["cases_passed"],
                      "cases_total": len(records), "receipt": str(output / "ADAPTER-CHALLENGE-RECEIPT.json")}))
    return 0 if receipt["pass"] else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    return run(args)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, OSError) as error:
        print(str(error), file=sys.stderr)
        sys.exit(1)
