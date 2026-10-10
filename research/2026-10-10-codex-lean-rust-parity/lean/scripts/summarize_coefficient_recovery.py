#!/usr/bin/env python3
"""Summarize preserved, actually accepted coefficient repair target runs.

Kernel acceptance, the explicit declaration audit and executable smoke are
reported independently. A pending or failed target never inherits a pass from
another target. Original delivery sources and failed attempts remain unchanged.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from check_core import COMPILER, save, sha

ROOT = Path(__file__).resolve().parents[1]
TARGETS = ["candidate/g7-coefficients", "evidence/g7-coefficients-explicit-audit",
           "evidence/g7-coefficient-codegen-smoke"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("workspace", type=Path)
    args = parser.parse_args()
    work = args.workspace.resolve()
    preparation = json.loads((work / "PREPARATION.json").read_bytes())
    evidence = Path(preparation["evidence"])
    targets = {}
    for label in TARGETS:
        accepted = []
        for run in sorted((work / ".build/runs").iterdir()):
            result_path = run / "targets" / label.replace("/", "_") / "RESULT.json"
            final_path = run / "FINAL-RECEIPT.json"
            if not result_path.exists() or not final_path.exists():
                continue
            result = json.loads(result_path.read_bytes())
            final = json.loads(final_path.read_bytes())
            if result["status"] != "PASS" or label not in final["targets_passed"]:
                continue
            assert final["status"] == "PASS_ALL_REQUESTED_TARGETS"
            assert final["compiler_identity_stable"]
            assert final["compiler_sha256"] == final["compiler_final_sha256"] == COMPILER
            assert final["native_runtime_final_rehash_stable"]
            for kind in ["aggregate_receipt", "audit_receipt"]:
                assert result[kind]["status"] == "PASS_FRESH_KERNEL_CHECK"
            frozen_run = evidence / ("run-" + run.name)
            assert (frozen_run / "PRESERVATION-MANIFEST.json").is_file(), "Preserve the run first."
            frozen_result = frozen_run / result_path.relative_to(run)
            assert frozen_result.read_bytes() == result_path.read_bytes()
            audit_path = Path(result["audit_receipt"]["receipt_directory"]) / "work/AUDIT-RESULT.json"
            audit = json.loads(audit_path.read_bytes())
            assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"]
            assert not audit["missing_modules"]
            assert audit["declaration_count"] == result["declarations"]
            assert audit["theorem_declaration_count"] == result["theorems"]
            row = {"status": "PASS", "run": str(run),
                   "preserved_evidence": str(frozen_run.relative_to(ROOT)),
                   "result_sha256": sha(frozen_result),
                   "graph_sha256": final["graph_sha256"],
                   "closure_modules": result["closure_modules"],
                   "owned_declarations": result["declarations"],
                   "owned_theorems": result["theorems"],
                   "current_run_components": final["counts"],
                   "aggregate_status": result["aggregate_receipt"]["status"],
                   "audit_status": result["audit_receipt"]["status"],
                   "owned_axioms": [], "nonstandard_axiom_rows": [],
                   "compiler_identity_stable": True, "native_runtime_identity_stable": True}
            if label.endswith("codegen-smoke"):
                component = next(r for r in result["component_receipts"]
                                 if r["module"] == "G7EffectiveCoefficientSmoke")
                stdout = Path(component["receipt_directory"]) / "stdout"
                assert stdout.is_file()
                body = stdout.read_text()
                assert body.splitlines() == ["(1 : Rat)/2", "1"], ("Unexpected compiled smoke outputs", body)
                row["observed_executable_outputs"] = body.splitlines()
                row["execution_scope"] = "Inherited two-copy population diagonal at X=1/2 and one-copy full-epoch mass at X=1/2; successful compiled #eval plus #guard."
            accepted.append(row)
        targets[label] = accepted[-1] if accepted else {"status": "NOT_ACCEPTED_IN_THIS_CONTEXT"}
    kernel_pass = targets[TARGETS[0]]["status"] == "PASS"
    all_pass = all(row["status"] == "PASS" for row in targets.values())
    receipt = {"status": "PASS_REPAIRED_COEFFICIENT_CHAIN_AUDIT_AND_EXECUTABLE_SMOKE" if all_pass
               else "PASS_REPAIRED_COEFFICIENT_CHAIN_KERNEL_AUDIT" if kernel_pass else "PENDING",
               "workspace": str(work), "preparation_sha256": sha(work / "PREPARATION.json"),
               "original_graph_sha256": preparation["original_graph_sha256"],
               "repaired_graph_sha256": preparation["repaired_graph_sha256"],
               "proof_derivative_sha256": preparation["derivative_source_sha256"],
               "compiler_sha256": COMPILER, "trust_level": 0, "kernel_checking": True,
               "targets": targets,
               "historical_sources_or_receipts_overwritten": False,
               "fresh_all_dependencies_claimed": False,
               "executable_definitions_changed_by_proof_repair": False,
               "default_heartbeat_limit_increased": False,
               "scope": "Original effective enumeration/population/full-epoch definitions with a separately pinned proof repair. Native whole-LAW quotient, source/observation admission and master G1-G7 closure remain separate."}
    save(evidence / "ACCEPTANCE-SUMMARY.json", receipt)
    save(ROOT / "COEFFICIENT-RECOVERY-CERTIFICATE.json", receipt)
    print(json.dumps({"status": receipt["status"], "targets": {
        k: {s: v[s] for s in ["status", "closure_modules", "owned_declarations", "owned_theorems"] if s in v}
        for k, v in targets.items()}}))


if __name__ == "__main__":
    main()
