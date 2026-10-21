#!/usr/bin/env python3
"""Actual stdio/MCP composition on public synthetic inputs, inside bounded CI Docker.

Canonical server/bridge/runtime/guard remain byte-identical. The container
provides the original guard's ordinary namespaced cgroup counter.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SERVER = ROOT/"applications/research-solver-interop/server.py"


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def session(output, messages, binary=None):
    command = [sys.executable, "-I", "-B", str(SERVER),
               "--repository", str(ROOT), "--output-root", str(output),
               "--wall-seconds", "10"]
    if binary is not None:
        command += ["--rust-binary", str(binary)]
    initialize = dict(jsonrpc="2.0", id=1, method="initialize",
                      params=dict(protocolVersion="2025-06-18", capabilities={},
                                  clientInfo=dict(name="public-support-regression", version="1")))
    initialized = dict(jsonrpc="2.0", method="notifications/initialized")
    payload = b"".join((json.dumps(m, separators=(",", ":"))+"\n").encode()
                       for m in [initialize, initialized, *messages])
    result = subprocess.run(command, input=payload, capture_output=True, timeout=90)
    if result.returncode != 0 or result.stderr:
        raise AssertionError("stdio server failed: "+result.stderr.decode(errors="replace"))
    responses = [json.loads(line) for line in result.stdout.splitlines()]
    assert len(responses) == 1+len(messages)
    assert responses[0]["result"]["protocolVersion"] == "2025-06-18"
    return {r["id"]:r for r in responses}


def call(identity, raw):
    return dict(jsonrpc="2.0", id=identity, method="tools/call",
                params=dict(name="research_solver_run", arguments=dict(request_json=raw)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--binary", type=Path, required=True)
    parser.add_argument("--image-ref", required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    manifest = json.loads((HERE/"SOURCE-MANIFEST.json").read_bytes())
    for entry in manifest["connector_source_pins"]:
        if sha((ROOT/entry["path"]).read_bytes()) != entry["sha256"]:
            raise ValueError("connector source mismatch: "+entry["path"])
    # This is a real namespaced kernel counter, never a fixture or substituted
    # Python state function. Preserve its availability as a separate host fact.
    counter = Path("/sys/fs/cgroup/memory.current")
    initial = counter.read_text().strip()
    assert initial.isdigit()

    raw_two = (HERE/"fixtures/two-check-request.json").read_text()
    raw_three = (HERE/"fixtures/three-check-request.json").read_text()
    invalid = json.loads(raw_two)
    invalid["input"]["coefficients"][0] = "1"
    invalid = json.dumps(invalid)
    duplicate = '{"schema":"unified_research_solver_v1","schema":"duplicate","task":"check_certificate","input":{}}'
    oversized = " "*262145
    messages = [
        dict(jsonrpc="2.0", id=2, method="tools/list"),
        dict(jsonrpc="2.0", id=3, method="tools/call",
             params=dict(name="research_solver_capabilities", arguments={})),
        call(4,raw_two), call(5,raw_three), call(6,invalid), call(7,duplicate), call(8,oversized)]
    responses = session(args.output/"normal", messages)
    assert {t["name"] for t in responses[2]["result"]["tools"]} == {
        "research_solver_capabilities","research_solver_run"}
    capabilities = responses[3]["result"]["structuredContent"]
    assert capabilities["provider_sources_available"] is True
    assert capabilities["native_runtime_authenticated"] is False
    records = []
    for identity, raw, status, cap in [
        (4,raw_two,"CHECKED_RATIONAL_CERTIFICATE",4),
        (5,raw_three,"CHECKED_RATIONAL_CERTIFICATE",6),
        (6,invalid,"REFUSED_REQUEST",None),(7,duplicate,"REFUSED_REQUEST",None),
        (8,oversized,"REFUSED_BRIDGE_REQUEST",None)]:
        wrapper = responses[identity]["result"]
        value = wrapper["structuredContent"]
        assert value["status"] == status, (identity,value)
        if status == "REFUSED_BRIDGE_REQUEST":
            assert value["runtime_result_authenticated"] is False
            assert value["execution"]["guard_started"] is False
        else:
            assert value["runtime_result_authenticated"] is True, (identity,value)
            runtime = value["runtime_result"]
            assert runtime["primary_request_sha256"] == sha(raw.encode())
            assert runtime["source_feasibility_certified"] is False
            assert runtime["general_G3_resolved"] is False
            if cap is not None:
                checked = runtime["delegate"]["result"]["certificate_result"]
                assert checked["positive_support_cardinality_at_most"] == cap
                assert checked["source_existence_certified"] is False
                assert wrapper["isError"] is False
            else:
                assert wrapper["isError"] is True
        records.append(dict(id=identity, status=status,
                            runtime_result_authenticated=value["runtime_result_authenticated"],
                            isError=wrapper["isError"], request_sha256=sha(raw.encode())))

    # The new proposer remains outside the original checker whitelist even
    # though this job has successfully built and tested it.
    rejected = session(args.output/"unapproved", [call(2,raw_two)], args.binary)[2]["result"]
    value = rejected["structuredContent"]
    assert value["status"] == "UNKNOWN"
    assert value["runtime_result_authenticated"] is True
    assert value["runtime_result"]["delegate"] is None
    assert "not an approved executed profile" in value["runtime_result"]["reason"]
    assert rejected["isError"] is False
    records.append(dict(id="new-binary-profile",status="UNKNOWN",
                        runtime_result_authenticated=True,isError=False,
                        new_binary_sha256=sha(args.binary.read_bytes()),
                        native_binary_executed=False))
    report = dict(schema="actual_mcp_support_composition_v1",all_passed=True,
                  protocol="2025-06-18",actual_stdio_server_processes=2,
                  actual_connector_run_calls=6,capability_and_tool_list_checked=True,
                  runtime_and_bridge_sources_unchanged=True,
                  container_image=args.image_ref,python_version=sys.version,
                  container_network="none",container_memory_bytes=2*1024**3,
                  actual_original_counter="cgroup-v2 namespaced memory.current",
                  native_profile_adopted=False,Lean_compiled=False,
                  source_existence_certified=False,records=records)
    (args.output/"RESULT.json").write_text(json.dumps(report,sort_keys=True,indent=2)+"\n")
    print(json.dumps(report,sort_keys=True))


if __name__ == "__main__":
    main()
