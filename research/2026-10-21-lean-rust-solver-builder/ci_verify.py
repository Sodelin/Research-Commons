#!/usr/bin/env python3
"""ONLINE-only public synthetic regression driver; no compiler/runner replacement.

Invoked under the existing guard. Captured child bytes stay in memory.
Only source pins, synthetic case identities and summarized outcomes are exported.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import types

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
OLD = ROOT / "research/2026-10-13-astra-unified-solver-0645z"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def source(name, path, expected=None):
    raw = path.read_bytes()
    if expected is not None and sha(raw) != expected:
        raise ValueError("source mismatch: "+path.name)
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(raw, str(path), "exec"), module.__dict__)
    return module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((HERE/"SOURCE-MANIFEST.json").read_bytes())
    for entry in manifest["files"]:
        raw = (HERE/entry["path"]).read_bytes()
        if len(raw) != entry["utf8_bytes"] or sha(raw) != entry["sha256"]:
            raise ValueError("proposal source mismatch: "+entry["path"])
    pins = {}
    for entry in manifest["source_pins"]:
        raw = (ROOT/entry["path"]).read_bytes()
        if sha(raw) != entry["sha256"]:
            raise ValueError("original source mismatch: "+entry["path"])
        pins[Path(entry["path"]).name] = entry["sha256"]
    checker = source("certificates", OLD/"certificates.py", pins["certificates.py"])
    emitter = source("emit_lean", OLD/"emit_lean.py", pins["emit_lean.py"])
    codec = source("support_codec", HERE/"codec.py")
    singleton_tests = source("singleton_cases", OLD/"test_native_generator.py",
                             manifest["regression_source_pins"]["test_native_generator.py"])
    binary = args.binary.resolve()
    binary_sha = sha(binary.read_bytes())
    records = []
    native_calls = 0

    def execute(raw):
        nonlocal native_calls
        if sha(binary.read_bytes()) != binary_sha:
            raise ValueError("binary changed before execution")
        native_calls += 1
        result = subprocess.run([str(binary)], input=raw, capture_output=True, timeout=5)
        if sha(binary.read_bytes()) != binary_sha:
            raise ValueError("binary changed after execution")
        return result

    def check_wire(raw, cap):
        result = execute(raw)
        expected = f"CHECKED_RATIONAL_CERTIFICATE support_cap={cap} source_existence=false\n".encode()
        assert result.returncode == 0 and result.stdout == expected and not result.stderr

    vectors = json.loads((HERE/"fixtures/native-cases.json").read_bytes())["cases"]
    counts = {"GENERATED_AND_CHECKED": 0, "UNKNOWN": 0, "REFUSED": 0}
    sample_output = None
    sample_request = None
    for vector in vectors:
        raw = (vector["request"] if "request" in vector else
               vector["request_repeat"]["text"]*vector["request_repeat"]["count"]).encode()
        result = execute(raw)
        expected = vector["expected"]
        if expected == "GENERATED_AND_CHECKED":
            assert result.returncode == 0 and not result.stderr
            assert sha(result.stdout) == vector["stdout_sha256"], vector["label"]
            parts = raw.decode().split()
            n = int(parts[1])
            obj = dict(schema="rational_support_acquisition_v1",
                       candidate_survivals=parts[2:2+n],
                       moments=parts[3+n:])
            checked_request = codec.request(json.dumps(obj).encode(), checker)
            assert codec.encode(checked_request).encode() == raw+b"\n"
            receiver = codec.decode(result.stdout, checked_request, checker)
            checked = checker.checked(receiver["input"])
            assert checked["positive_support_cardinality_at_most"] == 2*n
            assert checked["source_existence_certified"] is False
            emitted_wire = result.stdout.split(b"\n", 1)[1]
            assert checker.wire(receiver["input"]).encode() == emitted_wire
            check_wire(emitted_wire, 2*n)
            if sample_output is None and n == 2:
                sample_output, sample_request = result.stdout, checked_request
        elif expected == "UNKNOWN":
            assert result.returncode == 2 and not result.stderr
            assert result.stdout.startswith(b"UNKNOWN ") and result.stdout.endswith(b"source_existence=false\n")
        else:
            assert result.returncode == 1 and not result.stdout and result.stderr.startswith(b"REFUSED ")
        counts[expected] += 1
        records.append(dict(label=vector["label"], input_sha256=sha(raw),
                            expected=expected, exit_code=result.returncode, stdout_sha256=sha(result.stdout)))

    singleton_counts = {"GENERATED_AND_CHECKED": 0, "UNKNOWN": 0, "REFUSED": 0, "REFUSED_FRAME": 0}
    for name, moments in singleton_tests.cases():
        raw = ("COMMON_GENERATE_SINGLETON_V1 "+" ".join(moments)+"\n").encode()
        try:
            expected = checker.generate_singleton(moments)
        except checker.Refused:
            expected = dict(status="REFUSED")
        result = execute(raw)
        status = expected["status"]
        if status == "GENERATED_AND_CHECKED":
            expected_wire = checker.wire(expected["certificate"])
            assert result.returncode == 0 and not result.stderr
            assert result.stdout == ("GENERATED_AND_CHECKED support_cap=2 source_existence=false\n"+expected_wire).encode(), name
            check_wire(expected_wire.encode(), 2)
        elif status == "UNKNOWN":
            reason = ("generated_certificate_exceeds_supported_exact_language"
                      if expected["reason"] == "generated certificate exceeds supported exact language"
                      else "supplied_moments_do_not_fit_singleton_generator")
            assert result.returncode == 2 and not result.stderr
            assert result.stdout == ("UNKNOWN "+reason+" source_existence=false\n").encode(), name
        else:
            assert result.returncode == 1 and not result.stdout and result.stderr.startswith(b"REFUSED "), name
        singleton_counts[status] += 1
    mode = "COMMON_GENERATE_SINGLETON_V1"
    malformed_frames = [
        (mode+"\n").encode(), (mode+" 1 1/2\n").encode(),
        (mode+" 1 1/2 1/8 extra\n").encode(), (mode+" 1 1 / 2 1/8\n").encode(),
        b"COMMON_GENERATE_SINGLETON_V2 1 1/2 1/8\n",
        (mode+" 1 1/2 1/8\x00\n").encode(),
        (mode+" 1 1/2 1/8\n").encode()+b"\xff",
        (mode+" "+" "*(262145-len(mode)-1)).encode()]
    for raw in malformed_frames:
        result = execute(raw)
        assert result.returncode == 1 and not result.stdout and result.stderr.startswith(b"REFUSED ")
        singleton_counts["REFUSED_FRAME"] += 1

    codec_negative = 0
    bad_requests = [
        b'{"schema":"rational_support_acquisition_v1","schema":"x","candidate_survivals":[],"moments":[]}',
        b'{"schema":"rational_support_acquisition_v1","candidate_survivals":["1/2"],"moments":[1,0.5,0.125]}',
        b'NaN', b'\xff', b" "*(262145)]
    for raw in bad_requests:
        try:
            codec.request(raw, checker)
        except (checker.Refused, ValueError):
            codec_negative += 1
        else:
            raise AssertionError("malformed JSON accepted")
    assert sample_output is not None
    bad_outputs = [
        sample_output.replace(b"source_existence=false", b"source_existence=true", 1),
        sample_output.split(b"\n", 1)[1], sample_output+b"extra",
        sample_output[:sample_output.rfind(b" ")], sample_output+b"\xff",
        sample_output.replace(b"COMMON_CERT_V1 5", b"COMMON_CERT_V1 7", 1)]
    for raw in bad_outputs:
        try:
            codec.decode(raw, sample_request, checker)
        except (checker.Refused, ValueError):
            codec_negative += 1
        else:
            raise AssertionError("malformed native output accepted")
    changed_request = copy.deepcopy(sample_request)
    changed_request["moments"][1] = "2/2"
    try:
        codec.decode(sample_output, changed_request, checker)
    except checker.Refused:
        codec_negative += 1
    else:
        raise AssertionError("unbound moment vector accepted")

    proof_outputs = []
    for name in ["two", "three"]:
        receiver = checker.loads((HERE/f"fixtures/{name}-check-request.json").read_bytes())
        checked = checker.checked(receiver["input"])
        proof = emitter.render(receiver["input"]).encode()
        target = args.output/f"{name}-support.lean"
        target.write_bytes(proof)
        proof_outputs.append(dict(path=target.name, sha256=sha(proof), bytes=len(proof),
                                  certificate_sha256=checker.digest(receiver["input"]),
                                  checker_status=checked["status"], compiled=False))
    runtime = source("pinned_unified_runtime",
                     ROOT/"research/2026-10-13-astra-unified-runtime-2350z/runtime.py",
                     manifest["runtime_source_pin"]["sha256"])
    runtime_records = []
    cli_calls = 0
    for name, nodes in [("two",["1/3","2/3"]),("three",["1/4","1/2","3/4"])]:
        original_request = checker.loads((HERE/f"fixtures/{name}-check-request.json").read_bytes())
        acquisition = dict(schema="rational_support_acquisition_v1",
                           candidate_survivals=nodes, moments=original_request["input"]["moments"])
        incoming = json.dumps(acquisition).encode()
        bound_path = args.output/f"{name}-acquisition.json"
        bound_path.write_bytes(incoming)
        encoded = subprocess.run([sys.executable,"-I","-B",str(HERE/"codec.py"),"encode",
                                  "--repository",str(ROOT)],input=incoming,capture_output=True,timeout=5)
        cli_calls += 1
        assert encoded.returncode == 0 and not encoded.stderr
        proposed = execute(encoded.stdout)
        assert proposed.returncode == 0 and not proposed.stderr
        decoded = subprocess.run([sys.executable,"-I","-B",str(HERE/"codec.py"),"decode",
                                  "--repository",str(ROOT),"--request",str(bound_path)],
                                 input=proposed.stdout,capture_output=True,timeout=5)
        cli_calls += 1
        assert decoded.returncode == 0 and not decoded.stderr
        assert checker.loads(decoded.stdout) == original_request
        outcome = runtime.run(decoded.stdout,args.output/f"runtime-{name}")
        assert outcome["status"] == "CHECKED_RATIONAL_CERTIFICATE", outcome
        assert outcome["request_preserved"] is True
        assert outcome["primary_request_sha256"] == sha(decoded.stdout)
        assert outcome["source_feasibility_certified"] is False
        assert outcome["general_G3_resolved"] is False
        assert outcome["delegate"]["invoked"] and outcome["delegate"]["returned"]
        assert outcome["delegate"]["result"]["certificate_result"]["source_existence_certified"] is False
        runtime_records.append(dict(name=name,status=outcome["status"],literal_request_sha256=sha(decoded.stdout),
                                    certificate_sha256=checker.digest(original_request["input"]),
                                    provider_sources=outcome["authenticated_provider_sources"]))
    denied = runtime.run((HERE/"fixtures/two-check-request.json").read_bytes(),
                         args.output/"runtime-unapproved",rust_binary=binary)
    assert denied["status"] == "UNKNOWN" and denied["delegate"] is None
    assert "not an approved executed profile" in denied["reason"]
    runtime_records.append(dict(name="new-unapproved-binary",status="UNKNOWN",native_binary_executed=False))

    report = dict(schema="online_rust_support_validation_v1", binary_sha256=binary_sha,
                  native_support_cases=len(vectors), native_support_counts=counts,
                  singleton_cases=sum(singleton_counts.values()), singleton_counts=singleton_counts,
                  previous_accepted_binary_replayed=False,
                  scope="New proposer plus original Python; original historical binary not invoked",
                  codec_negative_controls=codec_negative, native_process_invocations=native_calls,
                  native_fixture_records_sha256=sha(json.dumps(records, sort_keys=True).encode()),
                  emitted_lean=proof_outputs, Lean_compiled=False,
                  source_existence_certified=False, native_refinement_proved=False,
                  actual_codec_cli_calls=cli_calls, canonical_runtime_cases=runtime_records,
                  all_passed=True)
    (args.output/"RESULT.json").write_text(json.dumps(report, indent=2, sort_keys=True)+"\n")
    print(json.dumps(report, sort_keys=True))


if __name__ == "__main__":
    main()
