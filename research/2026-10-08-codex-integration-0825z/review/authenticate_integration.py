"""Independent static review of other owners' saved evidence; no scientific execution."""
from collections import Counter
from fractions import Fraction
from pathlib import Path
import base64
import gzip
import hashlib
import json
import re
import subprocess

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
PACKET = HERE.parent
sha = lambda b: hashlib.sha256(b).hexdigest()
read_json = lambda p: json.loads(p.read_bytes())

def git_bytes(commit, path):
    return subprocess.check_output(["git", "show", f"{commit}:{path}"], cwd=REPO)

def save(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

# Read raw terminal transport independently rather than trusting recovered totals.
release = PACKET / "lean-release/terminal-37749239915"
run, jobs = read_json(release / "run.json"), read_json(release / "jobs.json")
commit = "916e02a1d51d79cdffd300b9d8313df2608b08bc"
assert run["id"] == 37749239915 and run["head_sha"] == commit
assert run["status"] == "completed" and run["conclusion"] == "success"
assert len(jobs["jobs"]) == 1
job = jobs["jobs"][0]
assert job["id"] == 113218106837 and job["conclusion"] == "success"
raw = (release / "gh-run-view.log").read_bytes()
serial = []
for line in raw.decode().splitlines():
    split = line.split("\t", 2)
    if len(split) == 3 and split[1] == "Verify G6 frozen sources serially":
        timestamp, sep, rest = split[2].partition(" ")
        assert sep and re.fullmatch(r"\ufeff?2026-10-08T\S+", timestamp)
        serial.append(rest)
def one(marker):
    found = [json.loads(s[len(marker):]) for s in serial if s.startswith(marker)]
    assert len(found) == 1
    return found[0]
inputs = one("G6_INPUTS ")
assert inputs == read_json(release / "inputs-recovered.json")
assert inputs["source_commit"] == commit
plan_path = "research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/freeze-plans/finite-corruption-direction-repair-static.json"
plan = json.loads(git_bytes(commit, plan_path))
assert inputs["targets"] == plan["targets"]
assert inputs["topological_order"] == plan["topological_order"]
assert inputs["dependencies"] == plan["actual_runtime_dependencies"]
assert set(inputs["modules"]) == set(plan["modules"])
source_checks = {}
for module, identity in inputs["modules"].items():
    p = plan["modules"][module]
    content = git_bytes(commit, p["repository_path"])
    assert sha(content) == identity["sha256"] == p["sha256"]
    source_checks[module] = {"path": p["repository_path"], "sha256": sha(content), "bytes": len(content)}
control_checks = []
for p in plan["controls"]:
    content = git_bytes(commit, p["repository_path"])
    assert len(content) == p["bytes"] and sha(content) == p["sha256"]
    blob = subprocess.check_output(["git", "rev-parse", f"{commit}:{p['repository_path']}"], cwd=REPO, text=True).strip()
    assert blob == p["git_blob_sha"]
    control_checks.append({"path": p["repository_path"], "sha256": sha(content), "bytes": len(content)})
receipts = [json.loads(s[len("G6_RECEIPT "):]) for s in serial if s.startswith("G6_RECEIPT ")]
assert len(receipts) == 184 and all(r["exit"] == 0 for r in receipts)
outputs = {}
for i, s in enumerate(serial):
    if not s.startswith("G6_COMMAND "):
        continue
    command = json.loads(s[len("G6_COMMAND "):])
    j = next(j for j in range(i + 1, len(serial)) if serial[j].startswith("G6_RECEIPT "))
    receipt = json.loads(serial[j][len("G6_RECEIPT "):])
    assert command["argv"] == receipt["argv"] and command["start"] == receipt["start"]
    if command["argv"][:3] == ["lake", "exe", "cache"]:
        continue  # Terminal cursor rendering is outside exact stdout recovery.
    lines = serial[i + 1:j]
    stdout = ("\n".join(lines) + ("\n" if lines else "")).encode()
    assert sha(stdout) == receipt["output_sha256"]
    outputs[command["argv"][-1]] = stdout
assert len(outputs) == 183
payload = one("G6_COMPLETE_ENVIRONMENT_PAYLOAD ")
start, end = serial.index("G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_BEGIN"), serial.index("G6_COMPLETE_ENVIRONMENT_GZIP_BASE64_END")
encoded = serial[start + 1:end]
assert all(re.fullmatch(r"[A-Za-z0-9+/]+={0,2}", s) for s in encoded)
raw_inventory = gzip.decompress(base64.b64decode("".join(encoded), validate=True))
assert len(raw_inventory) == payload["bytes"] and sha(raw_inventory) == payload["sha256"]
assert raw_inventory == (release / "complete-environment-inventory.json").read_bytes()
inventory = json.loads(raw_inventory)
rows = inventory["declarations"]
by_name = {r["name"]: r for r in rows}
standard = {"propext", "Classical.choice", "Quot.sound"}
assert len(by_name) == len(rows) == inventory["declaration_count"] == 4224
assert sum(r["kind"] == "theorem" for r in rows) == inventory["theorem_declaration_count"] == 2779
assert set(inventory["selected_modules"]) == set(inputs["modules"])
assert not inventory["owned_axioms"] and not inventory["nonstandard_axiom_rows"] and not inventory["missing_modules"]
assert all(r["module"] in inputs["modules"] and set(r["axioms"]) <= standard and isinstance(r["type_references"], list) and isinstance(r["body_references"], list) for r in rows)
baseline = REPO / "research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/evidence/g6-run-37738512508-PASS/complete-environment-inventory.json"
baseline_raw = baseline.read_bytes()
assert sha(baseline_raw) == "cf0a500c9e35831cd598d6f12edd4fc0e63b534a2ad4322eb6584981307944ba"
old = {r["name"]: r for r in json.loads(baseline_raw)["declarations"]}
assert len(old) == 4209 and all(by_name.get(n) == r for n, r in old.items())
added = [r for r in rows if r["name"] not in old]
assert len(added) == 15 and sum(r["kind"] == "theorem" for r in added) == 13
named_stdout = next(v for k, v in outputs.items() if k.endswith("DeclarationAudit.lean"))
named = {n: [a.strip() for a in ax.split(",") if a.strip()] for n, ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", named_stdout.decode(), re.S)}
named.update({n: [] for n in re.findall(r"'([^']+)' does not depend on any axioms", named_stdout.decode())})
assert len(named) == 513 and all(n in by_name and set(ax) <= standard for n, ax in named.items())
assert named == read_json(release / "named-axiom-audit.json")["declarations"]
template_path = "research/2026-10-05-dot-connected-modular-lean-workspace-2252z/package/scripts/AuditTemplate.lean"
template = git_bytes(commit, template_path).decode()
placeholder = '#["NanuqActualBridgeQuartetResolution", "NanuqActualQuartetPortBranching"]'
assert template.count(placeholder) == 1
template = template.replace(placeholder, "#[" + ", ".join(json.dumps(m) for m in inventory["selected_modules"]) + "]")
complete_source = "\n".join("import " + m for m in inventory["selected_modules"]) + "\n" + template
assert sha(complete_source.encode()) == payload["audit_source_sha256"]
save("LEAN-181-STATIC-AUTHENTICATION.json", {"status": "INDEPENDENT STATIC ACCEPT", "compiler_invoked": False,
    "run": run["id"], "job": job["id"], "commit": commit, "raw_log_sha256": sha(raw),
    "receipts": len(receipts), "zero_exits": len(receipts), "noncache_output_hashes": len(outputs),
    "cache_stdout_hash": "not claimed; actual zero-exit receipt preserved", "modules": len(inputs["modules"]),
    "named": len(named), "owned": len(rows), "theorems": 2779, "old_rows_exact": len(old), "new_rows": len(added),
    "new_module_kind_counts": dict(Counter((r["module"] + ":" + r["kind"]) for r in added)),
    "payload": payload, "source_checks": source_checks, "control_checks": control_checks,
    "scope": "finite pairwise PMF corruption plus actual completed-observation consumer; full biological wrong-source image/G6 excluded"})

# Static practical source/receipt authentication. Do not import or execute providers.
practical = PACKET / "practical"
recovery = read_json(practical / "RECOVERY.json")
for path, identity in recovery["files"].items():
    copied = (practical / identity["isolated_copy"]).read_bytes()
    original = git_bytes(recovery["commons_head"], path)
    assert copied == original and len(copied) == identity["bytes"] and sha(copied) == identity["sha256"]
build = read_json(practical / "logs/BUILD-RESULT.json")
assert build["status"] == "PASS" and build["cargo_commands_offline_locked"] and build["source_bytes_unchanged"]
for name, receipt in zip(["core-test", "signed-release", "signed-comparison"], build["commands"]):
    assert receipt["exit_code"] == 0 and not receipt["timeout"]
    assert sha((practical / "logs" / (name + ".stdout")).read_bytes()) == receipt["stdout_sha256"]
    assert sha((practical / "logs" / (name + ".stderr")).read_bytes()) == receipt["stderr_sha256"]
diff = practical / "signed-differential"
result, expected, cases = read_json(diff / "RESULT.json"), read_json(diff / "PYTHON-EXPECTED.json"), read_json(diff / "CASES.json")
native_lines = (diff / "geometry.stdout").read_text().splitlines()
physical = ["h", "u", "v", "rA", "rB", "rC", "rAB", "rR", "g"]
residuals = ["root", "root_time", "h", "g", "AB1", "AB2", "BB1"]
assert result["status"] == "PASS" and result["source_and_binary_unchanged"]
assert len(native_lines) == len(expected) == len(cases) == 39
for case, ref, line in zip(cases, expected, native_lines):
    f = line.split("\t")
    assert len(f) in (16, 58) and f[:2] == ["result", case["id"]]
    assert f[7:10] == [str(case["max_exp_calls"]), "c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace", "native_exact_interval_core"]
    assert f[10:16] == ["0"] * 6
    assert f[2] == ref["status"] and (None if f[3] == "-" else f[3]) == ref.get("refusal")
    assert [int(f[i]) for i in (4, 5, 6)] == [ref["scalar_exp_calls"], ref["precision_fractional_bits"], ref["arithmetic_max_bits"]]
    if len(f) == 58:
        assert {p: f[16+2*i:18+2*i] for i, p in enumerate(physical)} == ref["difference_intervals"]
        assert dict(zip(physical, f[34:43])) == ref["normalized_absolute_difference_bounds"]
        assert f[43] == ref["maximum_normalized_difference_bound"]
        assert {p: f[44+2*i:46+2*i] for i, p in enumerate(residuals)} == ref["signed_residuals"]
        maximum = max(Fraction(v) for v in f[34:43])
        assert maximum == Fraction(f[43])
        assert (f[2] == "CONDITIONAL_PAIR_WIDTH_CERTIFIED") == (maximum < Fraction(1, 20))
    else:
        assert "difference_intervals" not in ref
for name in ["geometry", "protocol", "row_limit"]:
    receipt = read_json(diff / (name + ".execution.json"))
    assert receipt["state"] == "TERMINAL" and receipt["exit_code"] == 0
    assert len((diff / (name + ".stdout")).read_bytes()) == receipt["stdout_bytes"]
    assert len((diff / (name + ".stderr")).read_bytes()) == receipt["stderr_bytes"] == 0
assert (diff / "protocol.stdout").read_text().splitlines() == result["protocol_controls"]["expected"]
assert (diff / "row_limit.stdout").read_text().splitlines() == ["protocol\t-\tPROBE_SHAPE"] * 96 + ["protocol\t-\tPROBE_ROWS"]
before, after = read_json(diff / "BEFORE.json"), read_json(diff / "AFTER.json")
assert before == after and before["binary_sha256"] == build["binary"]["sha256"] == result["binary_sha256"]
binary = Path(build["commands"][-1]["command"][-2])
assert sha(binary.read_bytes()) == build["binary"]["sha256"]
save("PRACTICAL-STATIC-AUTHENTICATION.json", {"status": "INDEPENDENT SOURCE/INSPECTED-ACTUAL-RECEIPT ACCEPT", "reviewer_executed_provider_or_receiver": False,
    "recovered_exact_files": len(recovery["files"]), "build_commands": build["commands"], "binary": build["binary"],
    "geometry_cases": 39, "geometry_differences": 0, "completed_geometry_cases": 13, "refusals": 26, "protocol_controls": 9,
    "row_limit_responses": 97, "source_and_binary_exact_before_after": True,
    "scientific_flags": {k: result[k] for k in ["new_source_forward_evaluations", "observation_rows_replayed", "data_confidence_certificate_issued", "outer_cover_validated", "mean_band_coverage_admitted", "compatible_source_existence_verified"]},
    "scope": "bounded fixture compatibility and conditional source-pair geometry only; full solver accuracy/open biological admission excluded"})
print(json.dumps({"lean": "181/513/4224/2779; all4209prior exact", "practical": "39 exact/0differences;9protocol+96rowlimit controls"}))

# Original-D full producer/independent checker: authenticate actual evidence and
# recompute physical UNION widths statically; do not rerun the numerical source.
original = practical / "original-multistage"
o = read_json(original / "RESULT.json")
staging = read_json(original / "STAGING.json")
request = read_json(original / "REQUEST.json")
old_root = REPO / "research/2026-10-05-dot-msci-original-domain-profile-localization-1621z"
old_request = read_json(old_root / "controls/distinct/REQUEST.json")
assert {k: v for k, v in request.items() if k not in {"budget", "provenance"}} == {k: v for k, v in old_request.items() if k not in {"budget", "provenance"}}
assert sha((original / "REQUEST.json").read_bytes()) == o["request_sha256"]
for identity in staging["authenticated_public_sources"]:
    content = git_bytes(identity["commit"], identity["public_path"])
    assert len(content) == identity["bytes"] and sha(content) == identity["sha256"]
    blob = subprocess.check_output(["git", "rev-parse", f"{identity['commit']}:{identity['public_path']}"], cwd=REPO, text=True).strip()
    assert blob == identity["git_blob"]
for identity in staging["selected_unchanged_runtime_files"]:
    recovered = practical / "recovered/jc-runtime" / identity["runtime_relative"]
    assert recovered.read_bytes() == (REPO / identity["public_path"]).read_bytes()
    assert sha(recovered.read_bytes()) == identity["sha256"]
for name, receipt in zip(["stage", "producer", "checker"], o["records"]):
    assert receipt["exit_code"] == 0 and not receipt["timeout"]
    assert sha((original / (name + ".stdout")).read_bytes()) == receipt["stdout_sha256"]
    assert sha((original / (name + ".stderr")).read_bytes()) == receipt["stderr_sha256"]
for name in ["producer", "checker"]:
    assert read_json(original / (name + ".stdout")) == o[name]
checker = o["checker"]
assert checker["status"] == "CONDITIONAL_UNION_WIDTH_CERTIFIED"
assert checker["details"]["complete_numeric_replay"] and not checker["details"]["cross_process_cache_reused"]
assert checker["details"]["stages_recomputed"] == 8 and checker["details"]["journal_frames"] == 17
assert len(checker["physical_cover"]) == 1 and len(checker["widths"]) == 9
ratios = {}
for coordinate, width in checker["widths"].items():
    lows = [Fraction(c["box"][coordinate][0]) for c in checker["physical_cover"]]
    highs = [Fraction(c["box"][coordinate][1]) for c in checker["physical_cover"]]
    actual_width = max(highs) - min(lows)
    domain = request["box"][coordinate]
    original_width = Fraction(domain[1]) - Fraction(domain[0])
    assert actual_width == Fraction(width["width"])
    ratio = actual_width / original_width
    assert ratio == Fraction(width["normalized_ratio"]) < Fraction(1, 20)
    ratios[coordinate] = str(ratio)
assert not checker["source_feasibility_certified"] and not checker["statistical_coverage_verified"] and not checker["parameter_accuracy_released"]
for journal in o["journal"]:
    raw = (original / "journal" / journal["name"]).read_bytes()
    assert len(raw) == journal["bytes"] and sha(raw) == journal["sha256"]
tamper = read_json(original / "TAMPER-CONTROL.json")
assert tamper["matches"] and tamper["checker"] == read_json(original / "tamper-checker.stdout")
assert tamper["checker"]["status"] == "RECOVERED_UNKNOWN"
assert all(Fraction(v["normalized_ratio"]) == 1 for v in tamper["checker"]["widths"].values())
for identity in read_json(old_root / "reviews/REPLAY-RECEIPT.json"):
    # terminal_sha256 refers to the old unredacted terminal, not the public
    # projection. Authenticate the actually public numerical checker stdout.
    content = (old_root / "controls" / identity["name"] / "checker.stdout").read_bytes()
    assert sha(content) == identity["independent_output_sha256"]
save("ORIGINAL-NINE-STATIC-AUTHENTICATION.json", {"status": "INDEPENDENT SOURCE/INSPECTED-ACTUAL-RECEIPT ACCEPT", "reviewer_reran_numeric_source": False,
    "old_prior": "2026-10-05-dot-msci-original-domain-profile-localization-1621z; source-specific AB-profile and conditional all-nine arithmetic width result reused",
    "authenticated_public_files": len(staging["authenticated_public_sources"]), "runtime_files": len(staging["selected_unchanged_runtime_files"]),
    "request_change_from_old_distinct": ["budget", "provenance"], "all9_actual_full_union_ratios": ratios,
    "maximum": str(max(map(Fraction, ratios.values()))), "stages": 8, "frames": 17, "cells": 1,
    "producer_seconds": o["records"][1]["wall_seconds"], "checker_seconds": o["records"][2]["wall_seconds"],
    "tamper_fallback_full_D": True, "statistical_coverage_verified": False, "source_feasibility_certified": False, "parameter_accuracy_released": False,
    "native_is_in_original_callgraph": False, "scope": "unchanged original full-domain conditional arithmetic fixture; not new data, biological confidence, generic input success, or novel inversion method"})
print(json.dumps({"original_nine": "all9 full union below1/20;8stages17frames;old prior reused", "max_ratio": str(max(map(Fraction, ratios.values())))}))
