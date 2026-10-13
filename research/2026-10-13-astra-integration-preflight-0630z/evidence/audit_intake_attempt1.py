"""Reproduce the bounded source/receipt intake. No compiler/native execution.

Exit 2 means the required physical provider is unavailable in selected1613.
Exit 1 means evidence authentication failed. Exit 0 is never a build acceptance.
"""
from pathlib import Path
import base64
import gzip
import hashlib
import io
import json
import resource
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
BASE = ROOT / "research/2026-10-12-dot-accepted-connected-union1613-1737z"
PARITY = ROOT / "research/2026-10-10-codex-lean-rust-parity"
OUT = HERE / "evidence"
MAX_PACKET = 8 * 1024**2
PROVIDERS = {
    "G4WholeProfileDetermination": "fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09",
    "G4ActualPositiveGridUniqueness": "ee5d196dc25a53b8d15957fcbaf9fdf13435b78eb03f8e66819d3f258f35b787",
    "G4ActualSparseCertificateExistence": "9ea04cbe390030381624d25b20be10751dff62f75d5d6e7752b88b9599a46418",
}
MISSING_NAME = "G4ProtectedCommonRepresentative"
MISSING_SHA = "0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def identity(data, row):
    require(len(data) == row["bytes"], "byte count mismatch")
    require(sha(data) == row["sha256"], "SHA256 mismatch")


def read_json(path):
    require(path.stat().st_size <= MAX_PACKET, "input exceeds intake cap")
    return json.loads(path.read_bytes())


def pin(path):
    data = path.read_bytes()
    return dict(path=str(path.relative_to(ROOT)), bytes=len(data), sha256=sha(data),
                git_blob=hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest())


def unbundle(envelope):
    require(envelope["expanded_bytes"] <= MAX_PACKET, "expanded packet exceeds cap")
    packed = base64.b64decode(envelope["payload"], validate=True)
    identity(packed, dict(bytes=envelope["gzip_bytes"], sha256=envelope["gzip_sha256"]))
    with gzip.GzipFile(fileobj=io.BytesIO(packed)) as stream:
        raw = stream.read(MAX_PACKET + 1)
    identity(raw, dict(bytes=envelope["expanded_bytes"], sha256=envelope["expanded_sha256"]))
    return json.loads(raw)


def embedded_bytes(row):
    if "content_utf8" in row:
        data = row["content_utf8"].encode()
    elif row["encoding"] == "utf-8":
        data = row["content"].encode()
    elif row["encoding"] == "exact_gzip_bytes_base64":
        data = base64.b64decode(row["content"], validate=True)
    else:
        raise ValueError("unsupported artifact encoding")
    identity(data, row)
    return data


def main():
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024**2, 512 * 1024**2))
    resource.setrlimit(resource.RLIMIT_CPU, (30, 30))
    resource.setrlimit(resource.RLIMIT_FSIZE, (16 * 1024**2, 16 * 1024**2))
    require(shutil.disk_usage(HERE).free >= 8 * 1024**3, "disk floor")
    graph = read_json(BASE / "DEPENDENCY-GRAPH.json")["targets"]["current/connected"]
    check = read_json(ROOT / "research/2026-10-13-dot-g2-unified-integration-0238z/CHECK-1613.json")
    aggregate = ("\n".join("import " + name for name in graph["roots"]) + "\n").encode()
    require(sha(aggregate) == check["aggregate_receipt"]["source_sha256"], "aggregate identity")
    for row in check["g2"]:
        name = row["module"]
        require(name in graph["roots"], "G2 not an explicit root: " + name)
        require(graph["modules"][name]["sha256"] == row["sha256"], "G2 source selection")
        require(sha((BASE / "source-store" / (row["sha256"] + ".lean")).read_bytes()) == row["sha256"], "G2 bytes")
        require(graph["modules"][name]["imports"] == row["imports"], "G2 imports")
    selected = {}
    def visit(name):
        if name not in graph["modules"] or name in selected:
            return
        row = graph["modules"][name]
        source = BASE / "source-store" / (row["sha256"] + ".lean")
        require(sha(source.read_bytes()) == row["sha256"], "provider dependency bytes")
        selected[name] = row
        for dep in row["imports"]:
            visit(dep)
    for name, digest in PROVIDERS.items():
        require(graph["modules"][name]["sha256"] == digest, "accepted provider selection")
        require(name in graph["roots"], "provider not explicit root")
        visit(name)
    require(MISSING_NAME not in graph["modules"], "baseline changed; reassess physical provider")
    code = PARITY / "rust/proposals/canonical-snapshot-decoder-20261011T0905Z"
    decoder = read_json(code / "COMPLETE-SOURCE-EXECUTION-AND-QC.json")
    decoder_artifacts = {r["path"]: embedded_bytes(r) for r in decoder["artifacts"]}
    for name in ["source_native_snapshot.rs", "native_snapshot_decode_tests.rs"]:
        matches = [v for k, v in decoder_artifacts.items() if k.endswith("/" + name)]
        require(len(matches) == 1 and matches[0] == (code / name).read_bytes(), "decoder source differs from receipt")
    envelope_path = PARITY / "quality/FULL-CONTINUATION-EVIDENCE-PACKET-20261011T0718Z.json"
    continuation = unbundle(read_json(envelope_path))
    history = {r["path"]: embedded_bytes(r) for r in continuation["artifacts"]}
    serial_source = PARITY / "rust/proposals/serial-full-history-control-20261011T0715Z/serial_early_late_history_tests.rs"
    matches = [v for k, v in history.items() if k.endswith("/serial_early_late_history_tests.rs")]
    require(len(matches) == 1 and matches[0] == serial_source.read_bytes(), "serial test source differs")
    serial_prefix = "serial-history-closed-form-native-root-20261011T0645Z/execution-1/"
    native_receipts = []
    for artifacts, marker in [(decoder_artifacts, "native-snapshot-decode-root"), (history, serial_prefix)]:
        for path, raw in artifacts.items():
            if marker in path and path.endswith(("compile/RECEIPT.json", "tests/RECEIPT.json")):
                rec = json.loads(raw)
                require(rec["exit_code"] == 0 and rec["status"] == "PASS_PROCESS_EXIT_ZERO", "historical native process failed")
                native_receipts.append(dict(path=path, sha256=sha(raw), exit_code=rec["exit_code"],
                                            status=rec["status"], started_utc=rec["started_utc"]))
    require(len(native_receipts) == 4, "expected two compile and two test receipts")
    correction = next(json.loads(v) for k, v in history.items() if serial_prefix in k and k.endswith("ADDITIVE-POSTCAPTURE-SUMMARY-CORRECTION.json"))
    require(correction["original_status_relabelled"] is False, "historical failure erased")
    require(correction["target_rerun_performed_by_correction"] is False, "correction scope changed")
    stdout = next(v.decode() for k, v in history.items() if serial_prefix in k and k.endswith("tests/stdout.txt"))
    require(stdout == correction["test_stdout_full_UTF8"], "corrected stdout mismatch")
    require("running 1 test\n" in stdout and "1 passed; 0 failed" in stdout, "single-test result")
    count = ROOT / "research/2026-10-07-rust-count-pilot"
    count_report = read_json(count / "evidence/check-report.json")
    for path, digest in count_report["source_sha256"].items():
        require(sha((count / path).read_bytes()) == digest, "count source mismatch")
    interval = ROOT / "research/2026-10-08-cloud-rust-interval-root-0000z"
    freeze = read_json(interval / "reports/cloud-differential/source-freeze.json")
    for path, row in freeze["inputs"].items():
        identity((interval / path).read_bytes(), row)
    interval_summary = read_json(interval / "reports/cloud-differential/run-once/summary.json")
    for name in ["stdin", "stdout", "stderr"]:
        path = interval / ("reports/cloud-differential/run-once/probe." + name + (".tsv" if name != "stderr" else ""))
        require(sha(path.read_bytes()) == interval_summary["process"][name + "_sha256"], "interval wire stream identity")
    report = dict(schema="astra_integration_intake_v1", status="BLOCKED_MISSING_PHYSICAL_PROVIDER",
                  base_commit="7239e89dea5caad68a54227cee3b44a7d9b96389",
                  inspected_checkout=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                  graph=pin(BASE / "DEPENDENCY-GRAPH.json"), aggregate_sha256=sha(aggregate),
                  g2_source_import_root_checks=len(check["g2"]), providers=PROVIDERS,
                  missing_provider=dict(module=MISSING_NAME, sha256=MISSING_SHA, source_authenticated_here=False),
                  decoder_envelope=pin(code / "COMPLETE-SOURCE-EXECUTION-AND-QC.json"),
                  continuation_envelope=pin(envelope_path), native_receipts=native_receipts,
                  serial_correction=dict(status=correction["status"], finite_control=correction["finite_control"],
                                         original_failed_outer_receipt=correction["original_failed_outer_receipt_preserved"],
                                         native_rerun=False),
                  decoder_source=pin(code / "source_native_snapshot.rs"), serial_test_source=pin(serial_source),
                  inherited_count_corpus=count_report["corpus_cases"], inherited_interval_corpus=interval_summary["case_count"],
                  available_executables={name: shutil.which(name) for name in ["lean", "lake", "rustc", "cargo"]},
                  fresh_compiler_execution=False, fresh_native_tests=False,
                  historical_receipt_authentication_only=True, universal_native_refinement=False)
    OUT.mkdir(exist_ok=True)
    (OUT / "INTAKE.json").write_text(json.dumps(report, indent=2) + "\n")
    (OUT / "AVAILABLE-PROVIDER-GRAPH.json").write_text(json.dumps(dict(
        scope="Closure of the three available providers only; not the unavailable physical provider closure",
        roots=list(PROVIDERS), modules=selected,
        external_imports=sorted({dep for r in selected.values() for dep in r["imports"] if dep not in graph["modules"]})), indent=2) + "\n")
    print(json.dumps(dict(status=report["status"], g2_checks=len(check["g2"]),
                         authenticated_historical_native_receipts=len(native_receipts),
                         compiler_execution=False, native_execution=False)))
    return 2


if __name__ == "__main__":
    sys.exit(main())
