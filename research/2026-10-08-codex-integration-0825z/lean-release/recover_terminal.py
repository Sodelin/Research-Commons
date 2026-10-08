"""Read-only authentication of a completed remote Lean run; never invokes Lean.

Usage: python recover_terminal.py
Inputs are the saved GitHub CLI log/run/jobs metadata and immutable Git blobs.
All generated output stays in this owner's terminal-37749239915 directory.
"""
from collections import Counter
from datetime import datetime, timezone
import base64
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OUT = HERE / "terminal-37749239915"
PACKET = "research/2026-10-07-cloud-g6-sol-ultra-1601z/verification"
COMMIT = "916e02a1d51d79cdffd300b9d8313df2608b08bc"
RUN = 37749239915
sha = lambda data: hashlib.sha256(data).hexdigest()

def git_bytes(path, commit=COMMIT):
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=REPO)

def write_json(name, data):
    (OUT / name).write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")

metadata = json.loads((OUT / "run.json").read_text())
jobs = json.loads((OUT / "jobs.json").read_text())
assert metadata["id"] == RUN and metadata["head_sha"] == COMMIT
assert metadata["status"] == "completed" and metadata["conclusion"] == "success"
assert len(jobs["jobs"]) == 1
assert jobs["jobs"][0]["id"] == 113218106837
assert jobs["jobs"][0]["status"] == "completed"
assert jobs["jobs"][0]["conclusion"] == "success"

# gh run view --log supplies a job/step tab prefix and one timestamp plus space.
# Remove only that outer transport, preserving each stdout byte represented by
# the line log. Hash authentication below rejects any accidental normalization.
raw_log = (OUT / "gh-run-view.log").read_bytes()
lines = []
for line in raw_log.decode().splitlines():
    fields = line.split("\t", 2)
    if len(fields) != 3 or fields[1] != "Verify G6 frozen sources serially":
        continue
    match = re.fullmatch(r"\ufeff?\d{4}-\d{2}-\d{2}T\S+ (.*)", fields[2])
    assert match, repr(line[:160])
    lines.append(match[1])
(OUT / "serial-normalized.log").write_text("\n".join(lines) + "\n")

def unique_json(marker):
    matches = [json.loads(line[len(marker):]) for line in lines if line.startswith(marker)]
    assert len(matches) == 1, marker
    return matches[0]

inputs = unique_json("G6_INPUTS ")
assert inputs["source_commit"] == COMMIT
plan = json.loads(git_bytes(PACKET + "/freeze-plans/finite-corruption-direction-repair-static.json"))
assert inputs["targets"] == plan["targets"]
assert inputs["topological_order"] == plan["topological_order"]
assert set(inputs["modules"]) == set(plan["modules"])
assert inputs["mathlib_roots"] == plan["mathlib_roots"]
assert inputs["dependencies"] == plan["actual_runtime_dependencies"]

def lean_imports(source):
    clean, depth, i = [], 0, 0
    while i < len(source):
        if source[i:i+2] == "/-": depth += 1; i += 2
        elif depth and source[i:i+2] == "-/": depth -= 1; i += 2
        elif depth:
            if source[i] == "\n": clean.append("\n")
            i += 1
        else: clean.append(source[i]); i += 1
    assert depth == 0
    imports = []
    for line in "".join(clean).splitlines():
        match = re.match(r"\s*(?:public\s+)?import\s+(.+)", line)
        if match: imports.extend(match[1].split("--")[0].split())
    return imports

source_records, sources = {}, {}
for module, record in inputs["modules"].items():
    path = plan["modules"][module]["repository_path"]
    data = git_bytes(path)
    assert sha(data) == record["sha256"] == plan["modules"][module]["sha256"], module
    text = data.decode()
    assert lean_imports(text) == record["imports"] == plan["modules"][module]["imports"], module
    sources[module] = text
    source_records[module] = {"path": path, "bytes": len(data), "sha256": sha(data),
        "git_blob": subprocess.check_output(["git", "rev-parse", f"{COMMIT}:{path}"], cwd=REPO, text=True).strip()}
control_records = []
for control in plan["controls"]:
    data = git_bytes(control["repository_path"])
    assert sha(data) == control["sha256"] and len(data) == control["bytes"]
    blob = subprocess.check_output(["git", "rev-parse", f"{COMMIT}:{control['repository_path']}"], cwd=REPO, text=True).strip()
    assert blob == control["git_blob_sha"]
    control_records.append(control)

receipts = [json.loads(line[11:]) for line in lines if line.startswith("G6_RECEIPT ")]
assert len(receipts) == 184 and all(r["exit"] == 0 for r in receipts)
outputs, output_records, command_records = {}, {}, []
for i, line in enumerate(lines):
    if not line.startswith("G6_COMMAND "): continue
    command = json.loads(line[len("G6_COMMAND "):])
    end = next(j for j in range(i+1, len(lines)) if lines[j].startswith("G6_RECEIPT "))
    receipt = json.loads(lines[end][11:])
    assert command["argv"] == receipt["argv"] and command["start"] == receipt["start"]
    # Cache progress uses terminal cursor/carriage rendering and cannot be
    # reconstructed byte-for-byte from the public line view. Every custom
    # elaboration and both audits must reproduce their receipt hash exactly.
    if command["argv"][:3] == ["lake", "exe", "cache"]:
        command_records.append({**receipt, "stdout_authenticated": False,
                                "reason": "cache progress rendering; imported objects are reuse"})
        continue
    body = lines[i+1:end]
    data = ("\n".join(body) + ("\n" if body else "")).encode()
    assert sha(data) == receipt["output_sha256"], (command["argv"], sha(data), receipt["output_sha256"])
    name = command["argv"][-1]
    outputs[name] = data
    output_records[name] = {"bytes": len(data), "sha256": sha(data), "receipt": receipt}
    command_records.append({**receipt, "stdout_authenticated": True})
assert len(outputs) == 183
assert len([c for c in command_records if "-o" in c["argv"]]) == 181
custom_commands = [c for c in command_records if "-o" in c["argv"]]
for module, command in zip(inputs["topological_order"], custom_commands):
    assert command["argv"][:6] == ["lake", "env", "lean", "--trust=0", "-j1", "-M4096"]
    assert command["argv"][-1].endswith("/" + inputs["modules"][module]["path"]), module
for command in command_records:
    duration = (datetime.fromisoformat(command["end"]) - datetime.fromisoformat(command["start"])).total_seconds()
    assert 0 <= duration <= 180
job = jobs["jobs"][0]
job_seconds = (datetime.fromisoformat(job["completed_at"].replace("Z", "+00:00")) - datetime.fromisoformat(job["started_at"].replace("Z", "+00:00"))).total_seconds()
assert 0 <= job_seconds <= 900
serial_seconds = (datetime.fromisoformat(receipts[-1]["end"]) - datetime.fromisoformat(receipts[0]["start"])).total_seconds()
assert "Downloaded: 3584 file(s) [attempted 3584/3584 = 100%" in "\n".join(lines)
assert "Decompressed 3584 file(s)" in lines

counts = unique_json("CLOUD_SELECTED_AXIOM_AUDIT_PASSED ")
assert sum(counts.values()) == 513 and counts == plan["named_counts"]
named = []
for module in inputs["targets"]:
    ns = re.search(r"^namespace\s+(\S+)\s*$", sources[module], re.M)
    assert ns
    names = [ns[1] + "." + n for n in re.findall(r"^(?:noncomputable\s+)?(?:def|theorem|lemma)\s+([A-Za-z0-9_']+)", sources[module], re.M)]
    assert len(names) == counts[module]
    named.extend(names)
assert len(named) == len(set(named)) == 513
named_output = outputs[next(k for k in outputs if k.endswith("/DeclarationAudit.lean") or k == "DeclarationAudit.lean")]
reports = {name: [a.strip() for a in axes.split(",") if a.strip()] for name, axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", named_output.decode(), re.S)}
reports.update({name: [] for name in re.findall(r"'([^']+)' does not depend on any axioms", named_output.decode())})
standard = {"propext", "Classical.choice", "Quot.sound"}
assert set(reports) == set(named)
assert all(set(axes) <= standard for axes in reports.values())
named_source = "\n".join("import " + module for module in inputs["targets"]) + "\n\n" + "\n".join("#print axioms " + name for name in named) + "\n"
(OUT / "DeclarationAudit-reconstructed.lean").write_text(named_source)

payload = unique_json("G6_COMPLETE_ENVIRONMENT_PAYLOAD ")
begin = lines.index("G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN")
end = lines.index("G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END")
payload_lines = lines[begin+1:end]
assert all(re.fullmatch(r"[A-Za-z0-9+/]+={0,2}", line) for line in payload_lines)
inventory_raw = gzip.decompress(base64.b64decode("".join(payload_lines)))
assert sha(inventory_raw) == payload["sha256"] and len(inventory_raw) == payload["bytes"]
inventory = json.loads(inventory_raw)
rows = inventory["declarations"]
assert inventory["declaration_count"] == len(rows) == 4224
assert inventory["theorem_declaration_count"] == sum(r["kind"] == "theorem" for r in rows) == 2779
assert len({r["name"] for r in rows}) == len(rows)
assert set(inventory["selected_modules"]) == set(inputs["modules"])
assert inventory["selected_modules"] == inputs["topological_order"]
assert not inventory["owned_axioms"] and not inventory["nonstandard_axiom_rows"] and not inventory["missing_modules"]
assert all(r["module"] in inputs["modules"] and "type_references" in r and "body_references" in r and set(r["axioms"]) <= standard for r in rows)
template_path = "research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean"
template = git_bytes(template_path).decode()
placeholder = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
assert template.count(placeholder) == 1
template = template.replace(placeholder, "#[" + ", ".join(json.dumps(m) for m in inventory["selected_modules"]) + "]")
complete_source = "\n".join("import " + m for m in inventory["selected_modules"]) + "\n" + template
assert sha(complete_source.encode()) == payload["audit_source_sha256"]
(OUT / "CompleteEnvironmentAudit-reconstructed.lean").write_text(complete_source)
(OUT / "complete-environment-inventory.json").write_bytes(inventory_raw)

baseline_path = REPO / PACKET / "evidence/g6-run-37738512508-PASS/complete-environment-inventory.json"
baseline_raw = baseline_path.read_bytes()
assert sha(baseline_raw) == "cf0a500c9e35831cd598d6f12edd4fc0e63b534a2ad4322eb6584981307944ba"
baseline = json.loads(baseline_raw)
old = {r["name"]: r for r in baseline["declarations"]}
new = {r["name"]: r for r in rows}
assert len(old) == 4209
removed = sorted(set(old)-set(new))
changed = sorted(n for n in set(old)&set(new) if old[n] != new[n])
assert not removed and not changed
added = [r for r in rows if r["name"] not in old]
assert len(added) == 15
assert {r["module"] for r in added} == {"UnifiedLean.G6.FiniteCorruptionBoundary", "ActualObservationCorruption"}
assert sum(r["kind"] == "theorem" for r in added) == 13
generated_names = [r["name"] for r in added if r["name"] not in named]
assert set(generated_names) == {
    "UnifiedLean.G6.FiniteProbability.tv.eq_1",
    "UnifiedLean.G6.FiniteCorruptionBoundary.midpointPMF._proof_1",
    "UnifiedLean.G6.FiniteCorruptionBoundary.midpointPMF._proof_2",
}
baseline_inputs = json.loads((REPO / PACKET / "evidence/g6-run-37738512508-PASS/inputs-recovered.json").read_text())
assert len(baseline_inputs["modules"]) == 179
assert all(inputs["modules"][m] == r for m, r in baseline_inputs["modules"].items())

old_inputs = json.loads((REPO / PACKET / "evidence/g6-run-37743712528-FAILED/inputs-recovered.json").read_text())
changed_modules = sorted(m for m in inputs["modules"] if inputs["modules"][m] != old_inputs["modules"][m])
assert changed_modules == ["UnifiedLean.G6.FiniteCorruptionBoundary"]
assert inputs["modules"][changed_modules[0]]["sha256"] == "6b5964de36b9cc4f2e79d4d7e8652498b8f2517e98769c1b9aa6938bf197754a"
assert inputs["modules"]["ActualObservationCorruption"]["sha256"] == "201fe29b7efb33277625da5515cd5659f8f60a471c91d86b366c303ba55fc754"

for module in ["UnifiedLean.G6.FiniteCorruptionBoundary", "ActualObservationCorruption"]:
    command_path = inputs["modules"][module]["path"]
    key = next(k for k in outputs if k.endswith("/" + command_path) or k == command_path)
    (OUT / (module.split(".")[-1] + "-actual.log")).write_bytes(outputs[key])
for audit in ["DeclarationAudit", "CompleteEnvironmentAudit"]:
    key = next(k for k in outputs if k.endswith("/" + audit + ".lean") or k == audit + ".lean")
    (OUT / (audit + "-actual.log")).write_bytes(outputs[key])
write_json("inputs-recovered.json", inputs)
write_json("receipts-recovered.json", command_records)
write_json("noncache-stdout-authentication.json", output_records)
write_json("source-authentication.json", {"modules": source_records, "controls": control_records})
write_json("named-axiom-audit.json", {"count": 513, "module_counts": counts, "declarations": reports,
    "source_sha256": sha(named_source.encode()), "stdout_sha256": sha(named_output)})
write_json("prior-owned-row-comparison.json", {"baseline_run": 37738512508, "baseline_commit": "62e937a2b58f00f6ed1197133650b6da2f96f71f",
    "baseline_inventory_sha256": sha(baseline_raw), "current_run": RUN, "current_commit": COMMIT,
    "all_4209_prior_rows_exact": True, "removed": removed, "changed": changed, "added_rows": added,
    "historical_generated_helper_exception": "171→175 calendarTail.eq_def origin change preserved as the established179 state; no new drift"})
manifest = {
    "identifier": "INTEGRATION-LEAN-RELEASE-37749239915-20261008",
    "observed_at": datetime.now(timezone.utc).isoformat(), "contributor": "Codex integration role5 Lean release",
    "status": "PASS independent static terminal/source/axiom/full-row authentication; parent reviewer and original canonical publication separate",
    "run": RUN, "job": 113218106837, "frozen_commit": COMMIT, "result": "success",
    "remote_started_at": metadata["run_started_at"], "remote_completed_at": jobs["jobs"][0]["completed_at"],
    "actual_receipts": len(receipts), "zero_exits": len(receipts), "custom_modules": 181,
    "selected_declarations": 513, "owned_declarations": 4224, "theorem_declarations": 2779,
    "kind_counts": dict(Counter(r["kind"] for r in rows)), "payload": payload,
    "authenticated_noncache_stdout": len(outputs), "cache_stdout_authentication": "excluded line rendering; one zero-exit receipt retained",
    "standard_axioms": sorted(standard), "owned_axioms": [], "nonstandard_axiom_rows": [], "missing_modules": [],
    "prior_owned_rows_exact": 4209, "new_owned_rows": 15, "new_owned_theorems": 13,
    "new_written_theorems": 10, "new_written_definitions": 2, "new_generated_theorem_rows": generated_names,
    "new_module_counts": dict(Counter(r["module"] for r in added)), "changed_sources_vs_failed181": changed_modules,
    "runtime": inputs["dependencies"], "runtime_archive_sha256": "890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235",
    "caps": {"job_seconds": 900, "command_seconds": 180, "flags": ["--trust=0", "-j1", "-M4096"]},
    "actual_job_seconds": job_seconds, "actual_serial_seconds": serial_seconds,
    "cache_scope": {"historical_metadata_objects": 3302, "broader_source_pins": 3584,
                    "actual_downloaded_decompressed_objects": 3584,
                    "warning": "cache objects and source pins are different sets despite equal counts"},
    "launch_owner": "Original CLOUD-G6 sole Lean owner; no scheduling ownership handoff",
    "authorization": "dc1186 ONE gate consumed by this successful run; no retry/new compiler authorized here",
    "prior_failures": {"run": 37743712528, "finite_corruption": "whole25d5 module failed, seven sorryAx recovery reports rejected",
                       "actual_observation": "dependency blocked; no compiler command"},
    "scope_limits": ["finite pairwise generic-PMF corruption overlap and actual natural completed observation margin only",
        "native wrong biological source image, pruning/menu applicability, general G6/I_Z closure and effective executable tables remain separate",
        "new integration sources and AlphaGenome/CWU drafts outside this frozen run"],
    "compiler_invoked_locally": False, "archives_downloaded": False, "publication": "local owned artifacts only; root integrates/publishes",
    "input_artifacts": {"github_cli_log_sha256": sha(raw_log), "run_metadata_sha256": sha((OUT/"run.json").read_bytes()),
                        "jobs_metadata_sha256": sha((OUT/"jobs.json").read_bytes())},
}
write_json("release-manifest.json", manifest)
print(json.dumps({k: manifest[k] for k in ["status", "run", "custom_modules", "selected_declarations", "owned_declarations", "theorem_declarations", "authenticated_noncache_stdout", "prior_owned_rows_exact", "new_owned_rows", "new_module_counts"]}, indent=2))
