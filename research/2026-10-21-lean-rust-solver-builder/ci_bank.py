#!/usr/bin/env python3
"""ONLINE-only public synthetic exact-bank and existing-solver composition."""
import argparse
import copy
from fractions import Fraction
import json
from pathlib import Path
import random
import subprocess
import sys
from ci_verify import HERE, ROOT, OLD, source, sha
import bank_codec
import codec

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary",type=Path,required=True)
    parser.add_argument("--proposer",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=False)
    checker = source("certificates",OLD/"certificates.py",codec.CERT_SHA256)
    emitter = source("bank_original_emit_lean",OLD/"emit_lean.py",
                     "27264a92409966415094b902df8226e7a86f305c0cef148325c7f6f60795ae37")
    runtime = source("bank_original_runtime",ROOT/"research/2026-10-13-astra-unified-runtime-2350z/runtime.py",
                     "07c9e49cd05eea2ac9fe590a0f3b01c922da08deefc55f1c5ca01da4711e7f4b")
    binary, proposer = args.binary.resolve(), args.proposer.resolve()
    identities = {str(p):sha(p.read_bytes()) for p in (binary,proposer)}
    calls, cli_calls, records = 0,0,[]
    def execute(path,raw):
        nonlocal calls
        assert sha(path.read_bytes()) == identities[str(path)]
        result = subprocess.run([str(path)],input=raw,capture_output=True,timeout=5)
        assert sha(path.read_bytes()) == identities[str(path)]
        calls += 1
        return result
    def cli(script,mode,raw,extra=()):
        nonlocal cli_calls
        result = subprocess.run([sys.executable,"-E","-s","-B",str(HERE/script),mode,
                                 "--repository",str(ROOT),*map(str,extra)],
                                input=raw,capture_output=True,timeout=5)
        cli_calls += 1
        return result
    canonical_main = (OLD/"rust/src/main.rs").read_text()
    parser_body = canonical_main[canonical_main.index("struct Input<'a>"):canonical_main.index("\nfn add(")]
    assert parser_body in (HERE/"rust/src/bin/common-bank-moments.rs").read_text()
    rng = random.Random(20261021)
    cases = []
    for index in range(192):
        n = 1+index%16
        integer_weights = [rng.randint(0,7) for _ in range(n)]
        if not sum(integer_weights):
            integer_weights[0] = 1
        total = sum(integer_weights)
        atoms = [{"weight":str(Fraction(w,total)),
                  "survival":str(Fraction(rng.randint(1,8),8) if w else Fraction(-rng.randint(0,8),3))}
                 for w in integer_weights]
        cases.append({"schema":"rational_finite_bank_moments_v1",
                      "copy_level_count":1+index%8,"atoms":atoms})
    for name in ("two","three"):
        cases.append(json.loads((HERE/f"fixtures/{name}-bank.json").read_bytes()))
    for obj in cases:
        literal = json.dumps(obj,sort_keys=True).encode()
        bank_codec.request(literal,checker)
        raw = bank_codec.encode(obj).encode()
        result = execute(binary,raw)
        assert result.returncode == 0 and not result.stderr,(obj,result)
        report = bank_codec.decode(result.stdout,obj,checker,sha(literal))
        assert report["status"] == "CHECKED_RATIONAL_BANK_MOMENTS"
        assert report["exponents"] == [k*(k-1)//2 for k in report["copy_levels"]]
        # Atom permutation may change input stats/order, never the grouped law or moments.
        reverse = copy.deepcopy(obj)
        reverse["atoms"].reverse()
        reversed_result = execute(binary,bank_codec.encode(reverse).encode())
        assert reversed_result.returncode == 0 and reversed_result.stdout == result.stdout
        records.append({"request_sha256":sha(literal),"native_stdout_sha256":sha(result.stdout),
                        "distinct_nodes":report["distinct_nodes"],"level":obj["copy_level_count"]})
    refused = [
        b"", b"COMMON_BANK_MOMENTS_V1 0 1 1 1", b"COMMON_BANK_MOMENTS_V1 9 1 1 1",
        b"COMMON_BANK_MOMENTS_V1 1 0", b"COMMON_BANK_MOMENTS_V1 1 257",
        b"COMMON_BANK_MOMENTS_V1 01 1 1 1", b"COMMON_BANK_MOMENTS_V1 1 1 1 0.5",
        b"COMMON_BANK_MOMENTS_V1 1 1 1 1/0", b"COMMON_BANK_MOMENTS_V1 1 1 1",
        b"COMMON_BANK_MOMENTS_V1 1 1 1 1 extra", b"COMMON_BANK_MOMENTS_V1 3 1 1 0",
        b"COMMON_BANK_MOMENTS_V1 3 1 1 2", b"COMMON_BANK_MOMENTS_V1 3 2 -1 1/2 1 1/2",
        b"COMMON_BANK_MOMENTS_V1 3 1 0 1", b"COMMON_BANK_MOMENTS_V1 3 2 1/3 1/2 1/3 1/3",
        b"\xff",b" "*262145]
    for raw in refused:
        result = execute(binary,raw)
        assert result.returncode == 1 and not result.stdout and result.stderr.startswith(b"REFUSED ")
    result = execute(binary,b"COMMON_BANK_MOMENTS_V1 3 1 1 1/170141183460469231731687303715884105727")
    assert result.returncode == 2 and result.stdout == b"UNKNOWN derived_rational_output_cap source_existence=false\n" and not result.stderr
    negatives = 0
    literal = (HERE/"fixtures/two-bank.json").read_bytes()
    obj = bank_codec.request(literal,checker)
    result = execute(binary,bank_codec.encode(obj).encode())
    for changed in [result.stdout+b" ",result.stdout[:-1],result.stdout.replace(b"1/6",b"1/7"),
                    result.stdout.replace(b"5 4 3 2",b"5 4 4 2"),result.stdout+b"\xff"]:
        try:
            bank_codec.decode(changed,obj,checker,sha(literal))
        except checker.Refused:
            negatives += 1
        else:
            raise AssertionError("changed native result accepted")
    for raw in [literal.replace(b'"copy_level_count": 5',b'"copy_level_count": true'),
                literal.replace(b'"copy_level_count": 5',b'"copy_level_count": 5, "copy_level_count": 5'),
                literal.replace(b'"weight": "1/4"',b'"weight": "-1/4"',1)]:
        try:
            bank_codec.request(raw,checker)
        except checker.Refused:
            negatives += 1
        else:
            raise AssertionError("invalid JSON bank request accepted")
    # SOURCE follow-on controls; no execution until the real encrypted writer binds.
    original_bank = json.loads((HERE/"fixtures/two-bank.json").read_bytes())
    compact_bank = {"schema":"rational_finite_bank_moments_v1","copy_level_count":5,
                    "atoms":[{"weight":"1/2","survival":"1/3"},
                             {"weight":"1/2","survival":"2/3"}]}
    shorter_bank = copy.deepcopy(compact_bank)
    shorter_bank["copy_level_count"] = 1
    identity_reports = []
    for bank in (original_bank,compact_bank,shorter_bank):
        literal_bank = json.dumps(bank,sort_keys=True).encode()
        bank_codec.request(literal_bank,checker)
        answer = execute(binary,bank_codec.encode(bank).encode())
        assert answer.returncode == 0 and not answer.stderr
        verified = bank_codec.decode(answer.stdout,bank,checker,sha(literal_bank))
        assert verified["provenance"]["kind"] == "supplied_mathematical_law"
        assert verified["provenance"]["observation_binding"] is None
        assert verified["provenance"]["error_confidence_contract"] is None
        identity_reports.append(verified)
    assert len({row["scalar_law_sha256"] for row in identity_reports}) == 1
    assert len({row["literal_request_sha256"] for row in identity_reports}) == 3
    assert identity_reports[0]["moment_vector_sha256"] == identity_reports[1]["moment_vector_sha256"]
    assert identity_reports[1]["moment_vector_sha256"] != identity_reports[2]["moment_vector_sha256"]
    assert identity_reports[0]["candidate_request_sha256"] == identity_reports[1]["candidate_request_sha256"]
    assert identity_reports[2]["candidate_request_sha256"] is None
    chain = []
    binding_negative_controls = 0
    for name in ("two","three"):
        literal = (HERE/f"fixtures/{name}-bank.json").read_bytes()
        obj = bank_codec.request(literal,checker)
        incoming = cli("bank_codec.py","encode",literal)
        assert incoming.returncode == 0 and not incoming.stderr
        native = execute(binary,incoming.stdout)
        assert native.returncode == 0 and not native.stderr
        acquired = cli("bank_codec.py","decode",native.stdout,
                       ["--request",HERE/f"fixtures/{name}-bank.json","--emit","acquisition"])
        assert acquired.returncode == 0 and not acquired.stderr
        acquisition = codec.request(acquired.stdout,checker)
        bound = args.output/f"{name}-acquisition.json"
        bound.write_bytes(acquired.stdout)
        proposed_wire = cli("codec.py","encode",acquired.stdout)
        assert proposed_wire.returncode == 0 and not proposed_wire.stderr
        generated = execute(proposer,proposed_wire.stdout)
        assert generated.returncode == 0 and not generated.stderr
        decoded = cli("codec.py","decode",generated.stdout,["--request",bound])
        assert decoded.returncode == 0 and not decoded.stderr
        receiver = checker.loads(decoded.stdout)
        expected = checker.loads((HERE/f"fixtures/{name}-check-request.json").read_bytes())
        assert receiver == expected
        checker.checked(receiver["input"])
        proof = emitter.render(receiver["input"]).encode()
        target = args.output/f"{name}-bank-support.lean"
        target.write_bytes(proof)
        assert proof == (HERE/"generated"/("Certificate_"+checker.digest(receiver["input"])+".lean")).read_bytes()
        outcome = runtime.run(decoded.stdout,args.output/f"runtime-{name}")
        assert outcome["status"] == "CHECKED_RATIONAL_CERTIFICATE" and outcome["request_preserved"] is True
        assert outcome["primary_request_sha256"] == sha(decoded.stdout)
        assert outcome["source_feasibility_certified"] is False and outcome["general_G3_resolved"] is False
        bound_result = bank_codec.bind_checked_certificate(literal,native.stdout,decoded.stdout,outcome,checker)
        assert bound_result["certificate_sha256"] == checker.digest(receiver["input"])
        assert bound_result["complete_original_runtime_return"] is outcome
        for alteration, altered_outcome in enumerate((copy.deepcopy(outcome),copy.deepcopy(outcome))):
            if alteration == 0:
                altered_outcome["primary_request_sha256"] = "0"*64
            else:
                altered_outcome["delegate"]["result"]["certificate_result"]["certificate_sha256"] = "0"*64
            try:
                bank_codec.bind_checked_certificate(literal,native.stdout,decoded.stdout,altered_outcome,checker)
            except checker.Refused:
                binding_negative_controls += 1
            else:
                raise AssertionError("unbound/altered runtime certificate outcome accepted")
        chain.append({"name":name,"bank_literal_sha256":sha(literal),
                      "acquisition":acquisition,"original_request_matches_published_fixture":True,
                      "scalar_law_sha256":bound_result["scalar_law_sha256"],
                      "moment_vector_sha256":bound_result["moment_vector_sha256"],
                      "candidate_request_sha256":bound_result["candidate_request_sha256"],
                      "provenance":bound_result["provenance"],
                      "copy_levels":bound_result["copy_levels"],"exponents":bound_result["exponents"],
                      "certificate_sha256":checker.digest(receiver["input"]),
                      "emitted_source_sha256":sha(proof),"emitted_source_bytes":len(proof),
                      "runtime_status":outcome["status"],"runtime_literal_request_sha256":sha(decoded.stdout),
                      "Lean_compiled":False})
    native_dir = args.output/"native"
    native_dir.mkdir()
    native_objects = []
    for executable in (binary,proposer):
        raw_object = executable.read_bytes()
        assert sha(raw_object) == identities[str(executable)]
        assert raw_object[:6] == b"\x7fELF\x02\x01"
        assert int.from_bytes(raw_object[18:20],"little") == 62
        snapshot = native_dir/executable.name
        snapshot.write_bytes(raw_object)
        assert sha(snapshot.read_bytes()) == identities[str(executable)]
        native_objects.append({"path":"native/"+executable.name,
                               "bytes":len(raw_object),"sha256":sha(raw_object),
                               "format":"ELF64 little-endian x86_64",
                               "tested_host":"GitHub Ubuntu24.04 x86_64",
                               "compiler":"official Rust1.90.0",
                               "canonical_profile_adopted":False})
    (args.output/"NATIVE-OBJECTS.json").write_text(json.dumps(native_objects,indent=2,sort_keys=True)+"\n")
    report = {"schema":"actual_rational_bank_native_composition_v1","all_passed":True,
              "binary_sha256":identities[str(binary)],"proposer_sha256":identities[str(proposer)],
              "native_objects":native_objects,"strict_parser_byte_copy_checked":True,"positive_bank_cases":len(cases),
              "reversal_controls":len(cases),"native_refusals":len(refused),
              "native_output_cap_unknowns":1,"codec_negative_controls":negatives,
              "actual_native_processes":calls,"actual_codec_cli_calls":cli_calls,
              "provenance_identity_controls":len(identity_reports),
              "runtime_binding_negative_controls":binding_negative_controls,
              "case_records_sha256":sha(json.dumps(records,sort_keys=True).encode()),
              "bank_to_native_to_original_runtime":chain,"canonical_source_changed":False,
              "source_existence_certified":False,"native_refinement_proved":False,"Lean_compiled":False}
    (args.output/"RESULT.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
    print(json.dumps(report,sort_keys=True))

if __name__ == "__main__":
    main()
