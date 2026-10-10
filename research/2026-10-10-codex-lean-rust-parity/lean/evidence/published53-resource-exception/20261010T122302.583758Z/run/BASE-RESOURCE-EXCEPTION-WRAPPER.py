#!/usr/bin/env python3
"""Recheck the exact historical337 audit with a separately recorded 6 GiB cap.

The publisher's graph, source versions, core and qualified wrapper stay intact.
Only the generated 825/base aggregate/audit resource cap changes; both retain
180 seconds, one Lean worker, trust zero and full owned-declaration coverage.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import shutil
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]
WRAPPER_SHA = "7ccbd4bca21115de3918331e9b5ea24ab47b610d98f0236b0f1b241d130f309a"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    parser.add_argument("--prior-run", type=Path, required=True)
    args = parser.parse_args()
    work = args.workspace.resolve()
    prior = args.prior_run.resolve()
    assert prior.is_relative_to(work / ".build/runs")
    final = json.loads((prior / "FINAL-RECEIPT.json").read_bytes())
    assert final["status"] == "INCOMPLETE_TARGET_FAILURES_PRESERVED"
    failed = json.loads((prior / "targets/825_base/RESULT.json").read_bytes())
    assert failed["status"] == "FAILED_OR_BLOCKED"
    failures = []
    for path in (prior / "attempts").glob("*/receipt.json"):
        rec = json.loads(path.read_bytes())
        if rec["status"] != "PASS_FRESH_KERNEL_CHECK" and rec["kind"] == "complete-owned-audit":
            if rec["working_directory"].startswith(str(prior)) and rec["source_sha256"]:
                failures.append((path, rec))
    wrapper_path = work / "scripts/build_resource_qualified.py"
    assert sha(wrapper_path) == WRAPPER_SHA
    spec = importlib.util.spec_from_file_location("unchanged_published_resource_policy", wrapper_path)
    published = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(published)
    graph, required, _ = published.verify_inputs()
    target = graph["targets"]["825/base"]
    assert len(target["order"]) == len(target["roots"]) == 337
    expected = published.sources_for(target, (work / "scripts/AuditTemplate.lean").read_text())
    failures = [(path, rec) for path, rec in failures if rec["source_sha256"] == expected["complete-owned-audit"]]
    assert len(failures) == 1
    failed_path, failed_rec = failures[0]
    assert failed_rec["cap_memory_mib"] == 4096 and failed_rec["cap_seconds"] == 180
    assert failed_rec["source_and_imports_stable"] and failed_rec["native_initialized_libraries_bound"]
    spec = importlib.util.spec_from_file_location("unchanged_published_core_for_base_exception", work / "scripts/build_connected.py")
    core = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(core)
    published.EXCEPTIONS = dict(published.EXCEPTIONS, **{"825/base": (337, 180)})
    builder = published.make_builder(core)()
    assert sha(builder.bin / "lean") == COMPILER
    identity = {"new_exception_target": "825/base", "modules": 337,
                "aggregate_and_complete_owned_audit_source_sha256": expected,
                "old_cap_memory_mib": 4096, "cap_memory_mib": 6144, "cap_seconds_each": 180,
                "minimum_available_memory_mib": 7168, "safety_reserve_mib": 1024,
                "old_failed_receipt": str(failed_path), "old_failed_receipt_sha256": sha(failed_path),
                "unchanged_published_wrapper_sha256": WRAPPER_SHA,
                "new_wrapper_sha256": sha(Path(__file__)), "graph_sha256": builder.graph_sha,
                "source_or_import_or_audit_coverage_changes": False,
                "original_frozen_53_replay_status_overwritten": False}
    save(builder.run / "BASE-RESOURCE-EXCEPTION-IDENTITY.json", identity)
    shutil.copyfile(Path(__file__), builder.run / "BASE-RESOURCE-EXCEPTION-WRAPPER.py")
    code = builder.run_targets(["825/base"])
    stable = sha(builder.bin / "lean") == COMPILER and sha(wrapper_path) == WRAPPER_SHA
    checked = {"status": "PASS_EXACT_337_CONTEXT_WITH_SEPARATE_6GIB_EXCEPTION" if code == 0 and stable else "INCOMPLETE_EXCEPTION_FAILURE_PRESERVED",
               "actual_run": str(builder.run), "resource_identity": identity,
               "counts": dict(builder.counts), "compiler_and_frozen_wrapper_final_stable": stable,
               "native_runtime_final_stable": core.read(builder.run / "FINAL-RECEIPT.json")["native_runtime_final_rehash_stable"],
               "scope": "Exact historical337 context. This separate pass does not rewrite the failed original4GiB receipt or by itself establish the other52 profile passes."}
    save(builder.run / "BASE-RESOURCE-EXCEPTION-FINAL.json", checked)
    save(ROOT / "BASE-RESOURCE-EXCEPTION-RESULT.json", checked)
    print(json.dumps({k: checked[k] for k in ["status", "actual_run", "counts"]}))
    return 0 if code == 0 and stable else 1


if __name__ == "__main__":
    raise SystemExit(main())
