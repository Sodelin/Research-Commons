#!/usr/bin/env python3
"""Review the saved 122/123/1504 survival-chain audits and inherited metadata.

No compiler or mathematical evaluator is invoked. Incomplete phase receipts are
rejected; authenticated component reuse is disclosed separately from fresh roots.
"""
from __future__ import annotations
import argparse
from collections import Counter
from datetime import datetime, timezone
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re

from review_preserved_run import review as preservation_review
from review_support_join import checked

PACKET = Path(__file__).resolve().parents[1]
CORE = "13ee72208587df0bd417c060df93d00d494c0e5c8e6c5c02e27f87f8a07123cc"
AUDIT = "f74a31db45c2bda1fc9acaa660dd21f28b84d2b7f4e9c8850603719f449fef6a"
GUARD = "4844ff0937b0c19bebca127ad317ea4ae5eb792b1e5f59d84c1dffaed34eb3f4"
PHASES = (("recovery/g7-original-survival-six", 122),
          ("recovery/g6-whole-edge-chart-consumer", 123), ("current/connected", 1504))
NEW = {"G7EdgeExposureAccounting", "G7CalendarExposureClosedForm",
       "G7OrderedFrontierProduct", "G7CalendarFrontierOrder",
       "G7WholeEdgeExposureInvariant", "G7OriginalSurvivalCoverage",
       "G6OriginalWholeEdgeChartConsumer"}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def load(path):
    return json.loads(path.read_bytes())


def review_transport(item, receipts, target_prefix):
    """Hash original/staged/installed companions and direct-import bundles."""
    aliases = item.json("preparation/CACHE-INSTALL-ALIASES.json")
    by_module = {r["module"]: r for r in aliases["entries"]}
    plan = item.json("preparation/CACHE-TRANSPORT-PRE-USE-PLAN.json")
    installs = [json.loads(line) for line in item.raw("CACHE-INSTALL-TRANSPORT-CHECKS.jsonl").splitlines()]
    installed = {r["destination"]: r for r in installs}
    if len(installed) != len(installs):
        raise ValueError("Duplicate cache installation destination")
    hashed = {}

    def hash_file(path, expected):
        path = Path(path)
        if path not in hashed:
            hashed[path] = sha(path.read_bytes())
        if hashed[path] != expected:
            raise ValueError("Transport identity mismatch: " + str(path))

    def check_bundle(path, expected):
        base = str(path)[:-len(".olean")]
        observed = {}
        for suffix in (".olean", ".olean.private", ".olean.server", ".ilean", ".ir"):
            candidate = Path(base + suffix)
            if candidate.is_file():
                if suffix not in expected:
                    raise ValueError("Unrecorded object companion: " + str(candidate))
                hash_file(candidate, expected[suffix])
                observed[suffix] = hashed[candidate]
        if observed != expected:
            raise ValueError("Missing declared object companion: " + str(path))

    for entry in plan["entries"]:
        for row in entry["files"]:
            for key in ("source", "destination"):
                hash_file(row[key], row["sha256"])
                if Path(row[key]).stat().st_size != row["bytes"]:
                    raise ValueError("Cache transport size mismatch")
    fresh, alias_count = 0, 0
    run = Path(item.manifest["actual_run"])
    for name, receipt in receipts.items():
        original = receipt["cached_object"]
        staged = original
        if name in by_module:
            row = by_module[name]
            if row["original_cached_object"] != original or row["object_artifacts"] != receipt["object_artifacts"]:
                raise ValueError("Cache alias context mismatch: " + name)
            for key in ("original_receipt", "staged_receipt"):
                hash_file(row[key], row["receipt_sha256"])
                if load(Path(row[key])) != receipt:
                    raise ValueError("Cache alias receipt mismatch: " + name)
            staged = row["staged_cached_object"]
            alias_count += 1
        else:
            original_receipt = Path(original).parent / "receipt.json"
            if load(original_receipt) != receipt:
                raise ValueError("New component cache receipt mismatch: " + name)
            fresh += 1
        out = run / target_prefix / "objects" / (name.replace(".", "/") + ".olean")
        for path in (original, staged, out):
            check_bundle(path, receipt["object_artifacts"])
        installation = installed[str(out)]
        if (installation["original_object"] != original or installation["install_source"] != staged
                or installation["object_artifacts"] != receipt["object_artifacts"]
                or not installation["original_and_staged_pre_post_checks_pass"]):
            raise ValueError("Installation context mismatch: " + name)
        for binding in receipt["direct_import_bindings"].values():
            check_bundle(binding["path"], binding["artifacts"])
    return {"pass": True, "selected_components": len(receipts), "alias_components": alias_count,
            "new_current_context_cache_components": fresh, "distinct_files_rehashed": len(hashed),
            "compiler_or_evaluator_called": False}


class Evidence:
    def __init__(self, path):
        self.path = path
        self.manifest = load(path)
        self.base = PACKET / "lean" / self.manifest["evidence"]
        self.records = {r.get("restored_path", r["path"]): r for r in self.manifest["preserved_files"]}

    def raw(self, relative):
        row = self.records[relative]
        data = (self.base / row["path"]).read_bytes()
        if len(data) != row["bytes"] or sha(data) != row["sha256"]:
            raise ValueError("Changed preserved evidence: " + relative)
        return gzip.decompress(data) if row.get("encoding") == "gzip" else data

    def json(self, relative):
        return json.loads(self.raw(relative))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("primary", type=Path)
    parser.add_argument("secondary", type=Path)
    parser.add_argument("union", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    inputs = [Evidence(p.resolve()) for p in (args.primary, args.secondary, args.union)]
    preserved = [preservation_review(item.path) for item in inputs]
    old_cert_path = PACKET / "lean/HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json"
    old_cert = load(old_cert_path)
    if sha(old_cert_path.read_bytes()) != "87fc610c7d4ef52c064990f040e90791f6b34c37fff97ffa3e93b9b25a481750":
        raise ValueError("Accepted1497 certificate changed")
    old_ev = PACKET / "lean" / old_cert["evidence"]
    old_preparation = load(old_ev.parent / "PREPARATION.json")
    old_graph = load(old_ev / "DEPENDENCY-GRAPH.json")["targets"]["current/connected"]
    old_target = old_cert["targets"]["current/connected"]
    old_raw = gzip.decompress((old_ev / old_target["audit_distribution"]).read_bytes())
    if sha(old_raw) != old_target["audit_raw_sha256"]:
        raise ValueError("Accepted1497 audit changed")
    old_audit = json.loads(old_raw)
    public = load(PACKET / "lean/LATEST-PUBLIC-UNION-CERTIFICATE.json")
    parser_path = PACKET / "lean" / public["source_evidence"] / "IMPORT-PARSER.py"
    parser_pin = load(PACKET / "quality/LATEST-UNION-REVIEW.json")["import_parser_sha256"]
    if sha(parser_path.read_bytes()) != parser_pin:
        raise ValueError("Frozen import parser changed")
    spec = importlib.util.spec_from_file_location("frozen_survival_import_parser", parser_path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    errors = []
    phases = []
    final_inventory = None
    final_modules = None
    transports = []
    for item, (label, expected) in zip(inputs, PHASES):
        manifest = item.manifest
        final = manifest["final_receipt"]
        if manifest["status"] != "PASS_ALL_REQUESTED_TARGETS" or final["targets_passed"] != [label]:
            raise ValueError("Phase is not an accepted single-target run: " + label)
        graph = item.json("DEPENDENCY-GRAPH.json")
        selected = graph["targets"][label]
        target_prefix = "targets/" + re.sub("[^A-Za-z0-9_-]", "_", label) + "/"
        target = item.json(target_prefix + "RESULT.json")
        prep = item.json("preparation/PREPARATION.json")
        closure = item.json("preparation/SOURCE-CLOSURE.json")
        sources = {r["module"]: r for r in closure}
        receipts = {r["module"]: r for r in target["component_receipts"]}
        audit_output = target["audit_receipt"]["auxiliary_outputs"][0]
        audit_relative = Path(target["audit_receipt"]["receipt_directory"]).relative_to(
            Path(manifest["actual_run"])) / audit_output["path"]
        audit_raw = item.raw(str(audit_relative))
        if sha(audit_raw) != audit_output["sha256"]:
            raise ValueError("Raw audit identity mismatch: " + label)
        audit = json.loads(audit_raw)
        checks = {
            "complete_selected_context": target["status"] == "PASS"
                and len(receipts) == len(target["component_receipts"]) == expected
                and set(receipts) == set(selected["modules"]) == set(selected["order"])
                and audit["selected_modules"] == selected["order"]
                and target["closure_modules"] == expected,
            "complete_unique_owned_inventory": audit["declaration_count"] == len(audit["declarations"])
                == len({r["name"] for r in audit["declarations"]}) == target["declarations"]
                and audit["theorem_declaration_count"] == sum(r["kind"] == "theorem" for r in audit["declarations"])
                == target["theorems"] and all(r["module"] in receipts for r in audit["declarations"]),
            "no_owned_or_nonstandard_axioms_or_missing_modules": not audit["owned_axioms"]
                and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"],
            "fresh_aggregate_and_audit": all(checked(target[k], final["compiler_sha256"], final["native_runtime_digest"])
                and Path(target[k]["receipt_directory"]).is_relative_to(Path(manifest["actual_run"]))
                for k in ("aggregate_receipt", "audit_receipt")),
            "stable_strict_kernel_and_runtime": final["trust_level"] == 0 and final["kernel_checking"]
                and final["compiler_identity_stable"] and final["native_runtime_final_rehash_stable"],
            "unchanged_strict_core_and_guard": prep["builder_sha256"] == sha(item.raw("BUILDER.py")) == CORE
                and prep["audit_template_sha256"] == sha(item.raw("AuditTemplate.lean")) == AUDIT,
            "unchanged_owned_namespace_policy": prep["namespace_adapter_derivation"]["exact_owned_mathlib_source_pins"]
                == old_preparation["namespace_adapter_derivation"]["exact_owned_mathlib_source_pins"]
                and not prep["namespace_adapter_derivation"]["compiler_kernel_cache_and_resource_policies_changed"]
                and not prep["namespace_adapter_derivation"]["global_mathlib_and_native_artifacts_modified"],
            "exact_storage_wrapper_binding": sha(item.raw("NAMESPACE-OVERLAY-WRAPPER.py")) == prep["namespace_overlay_wrapper_sha256"]
                and sha(item.raw("AUTHENTICATED-OVERLAY-WRAPPER.py")) == prep["optimized_overlay_sha256"],
            "graph_binding": sha(item.raw("DEPENDENCY-GRAPH.json")) == final["graph_sha256"] == prep["graph_sha256"],
            "historical_evidence_preserved": not manifest["original_attempts_overwritten"]
                and not manifest["compiled_artifact_bytes_distributed"],
        }
        for name, model in selected["modules"].items():
            row = receipts[name]
            raw = Path(sources[name]["scratch_source"]).read_bytes()
            if sha(raw) != model["sha256"] or module.imports(raw.decode()) != model["imports"]:
                errors.append(label + ": source/import mismatch " + name)
            if (not checked(row, final["compiler_sha256"], final["native_runtime_digest"])
                    or row["source_sha256"] != model["sha256"]):
                errors.append(label + ": component authentication " + name)
            for imported in model["imports"]:
                if imported in receipts and row["direct_import_sha256"].get(imported) != receipts[imported]["object_sha256"]:
                    errors.append(label + ": compiled import " + name + " -> " + imported)
        guards = [item.json(k) for k in item.records if k.startswith("resource-guard/") and k.endswith("/RECEIPT.json")]
        run_plan = item.json("preparation/RESOURCE-AND-RUN-PLAN.json")
        checks["bounded_guard_completed"] = len(guards) == 1 and all(
            g["exit_code"] == 0 and g["abort_reason"] is None and g["monitor_error"] is None
            and g["monitor_sha256"] == GUARD and not g["resource_caps_kernel_flags_core_or_audit_changed"]
            and g["peak_distinct_inode_allocation_bytes"] < run_plan["scratch_abort_bytes"]
            and g["peak_nonreclaimable_estimate_bytes"] < run_plan["memory_abort_bytes"] for g in guards)
        transports.append(review_transport(item, receipts, target_prefix))
        errors.extend(label + ": " + key for key, ok in checks.items() if not ok)
        phases.append({"target": label, "modules": expected, "owned_declarations": audit["declaration_count"],
                       "theorems": audit["theorem_declaration_count"], "component_counts": final["counts"],
                       "checks": checks, "actual_run": manifest["actual_run"]})
        if label == "current/connected":
            final_inventory, final_modules = audit, selected["modules"]
    if set(final_modules) - set(old_graph["modules"]) != NEW:
        errors.append("Final library does not add exactly the seven frozen modules")
    if any(final_modules.get(k) != row for k, row in old_graph["modules"].items()):
        errors.append("Accepted1497 source/import graph records changed")
    old_names = {r["name"]: r for r in old_audit["declarations"]}
    new_names = {r["name"]: r for r in final_inventory["declarations"]}
    metadata_errors = []
    for name, row in old_names.items():
        observed = new_names.get(name)
        if observed is None or set(row) != set(observed) or any(
                Counter(row[k]) != Counter(observed[k]) if isinstance(row[k], list) else row[k] != observed[k]
                for k in row):
            metadata_errors.append(name)
    errors.extend("Changed inherited declaration metadata: " + name for name in metadata_errors)
    result = {"schema": "survival_union_saved_evidence_review_v1", "pass": not errors, "errors": errors,
              "observed_utc": datetime.now(timezone.utc).isoformat(), "reviewer_sha256": sha(Path(__file__).read_bytes()),
              "phases": phases, "preservation_reviews": preserved, "transport_reviews": transports,
              "prior_owned_declarations_compared": len(old_names),
              "added_owned_declaration_names": len(set(new_names) - set(old_names)),
              "new_source_pins": {name: final_modules[name]["sha256"] for name in sorted(NEW)},
              "compiler_or_evaluator_called": False, "master_complete": False,
              "universal_native_refinement_verified": False,
              "scope": "Complete saved phase/root audits, exact source/import/kernel contexts and retained1497 metadata. Component reuse and fresh aggregate/audit checks remain distinct. Original G6/G7 master and native refinement are not inferred."}
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"pass": result["pass"], "errors": errors[:20], "phases": phases,
                      "prior_owned_declarations_compared": len(old_names)}))
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
