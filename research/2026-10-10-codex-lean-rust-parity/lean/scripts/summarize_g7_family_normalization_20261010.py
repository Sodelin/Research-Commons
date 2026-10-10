#!/usr/bin/env python3
"""Bind separate fresh proof-root audits to their immutable exact contexts."""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
from pathlib import Path
from check_core import save, sha

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result", type=Path)
    parser.add_argument("--certificate", required=True)
    args = parser.parse_args()
    result_path = args.result.resolve()
    result = json.loads(result_path.read_bytes())
    work = Path(result["workspace"])
    evidence = ROOT / result["evidence"]
    preparation = json.loads((work / "PREPARATION.json").read_bytes())
    final = result["final_receipt"]
    assert final["status"] == "PASS_ALL_REQUESTED_TARGETS"
    assert final["native_runtime_final_rehash_stable"] and final["compiler_identity_stable"]
    graph = json.loads((work / "DEPENDENCY-GRAPH.json").read_bytes())
    assert sha(work / "DEPENDENCY-GRAPH.json") == preparation["graph_sha256"] == final["graph_sha256"]
    files = {r.get("restored_path", r["path"]): r for r in result["preserved_files"]}
    def read(relative):
        row = files[relative]
        path = evidence / row["path"]
        assert sha(path) == row["sha256"] and path.stat().st_size == row["bytes"]
        body = gzip.decompress(path.read_bytes()) if row.get("encoding") == "gzip" else path.read_bytes()
        assert hashlib.sha256(body).hexdigest() == row.get("restored_sha256", row["sha256"])
        assert len(body) == row.get("restored_bytes", row["bytes"])
        return json.loads(body)
    summaries = {}
    for label in final["targets_requested"]:
        target = graph["targets"][label]
        relative = "targets/" + "".join(c if c.isascii() and (c.isalnum() or c in "_-") else "_" for c in label) + "/RESULT.json"
        checked = read(relative)
        assert checked["status"] == "PASS"
        assert checked["aggregate_receipt"]["status"] == checked["audit_receipt"]["status"] == "PASS_FRESH_KERNEL_CHECK"
        audit_relative = str(Path(checked["audit_receipt"]["audit_output"]).relative_to(Path(result["actual_run"])))
        audit = read(audit_relative)
        assert audit["selected_modules"] == target["order"]
        assert not audit["owned_axioms"] and not audit["nonstandard_axiom_rows"] and not audit["missing_modules"]
        for module in target["order"]:
            source = work / "source-store" / (target["modules"][module]["sha256"] + ".lean")
            assert sha(source) == target["modules"][module]["sha256"] == preparation["source_pins"][module]
        summaries[label] = {"status": "PASS_FRESH_AGGREGATE_AND_COMPLETE_OWNED_AUDIT",
            "roots": target["roots"], "closure_modules": len(target["order"]),
            "owned_declarations": audit["declaration_count"], "owned_theorems": audit["theorem_declaration_count"],
            "owned_axioms": [], "nonstandard_axiom_rows": [], "missing_modules": [],
            "audit_raw_sha256": files[audit_relative].get("restored_sha256", files[audit_relative]["sha256"]),
            "audit_distribution": files[audit_relative]["path"],
            "aggregate_source_sha256": checked["aggregate_receipt"]["source_sha256"],
            "audit_source_sha256": checked["audit_receipt"]["source_sha256"],
            "source_and_import_bindings_stable": True}
    certificate = {"status": "PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS",
        "workspace": str(work), "actual_run": result["actual_run"], "evidence": result["evidence"],
        "preservation_manifest_sha256": sha(evidence / "PRESERVATION-MANIFEST.json"),
        "preparation_sha256": sha(work / "PREPARATION.json"), "graph_sha256": final["graph_sha256"],
        "source_pins": preparation["source_pins"], "derivatives": preparation["derivatives"],
        "contexts": preparation["contexts"], "targets": summaries, "counts": final["counts"],
        "kernel_checking": True, "trust_level": 0, "compiler_sha256": final["compiler_sha256"],
        "native_runtime_digest": final["native_runtime_digest"], "compiler_and_native_final_stable": True,
        "scope": "Exact new theorem statements over pinned original provider assumptions. Separate target declaration counts overlap and must not be added. This certificate supplies neither general native Rust refinement nor source admission, coverage, analytic inversion or G1-G7 master closure.",
        "historical_evidence_or_scientific_gates_promoted": False}
    closure = json.loads((work / 'SOURCE-CLOSURE.json').read_bytes())
    assert len(closure) == 172 and all(t['closure_modules'] == 168 for t in summaries.values())
    assert final['counts'] == {'cache_reuse': 167, 'fresh_components': 1}
    proposal_path = ROOT / 'proposals/reuse-integration-20261010T2138Z/family-normalization/PROPOSAL-FREEZE.json'
    proposal = json.loads(proposal_path.read_bytes())
    assert proposal['sha256'] == '81dcd9983e73eecd5f59caac14ee6231825fdd9ae25dd9cf64bafbc06b6f2f08'
    certificate.update(
        executable_target_modules=168,
        guard_complete_staging_graph_modules=172,
        protected_provider_context_executed=False,
        protected_provider_source_pins={r['module']: r['sha256'] for r in closure if r['module'].startswith('Mathlib.')},
        parent1504_certificate=proposal['accepted_parent_certificate'],
        parent1504_independent_QC=proposal['independent_parent_QC'],
        root_source_pin=proposal['sha256'],
        root_independent_saved_review_pending=True,
        scope='One supplied strict comparison calendar per original graph; one normalized positive bank per original source chosen before all original-ID rows/programmes/reset actions. Existing full-Code controlled completed-law equality yields entire original row, programme, response, Experiment and history equality. Source/network/registry/natural inheritance/common modes, supplied admission, target and legal/update fields remain the original definitions. No native source/DTO refinement, timed observation, QE/CAD or strategy extraction is proved; accepted1504 is not widened by this separate168-root certificate.',
        freshness_qualification='167 exact accepted parent components reused; one new source fresh kernel check plus fresh aggregate and complete168-module owned audit. Four additional protected Mathlib provider records are staging guards and are neither executed as a target nor added to its owned counts.')
    path = ROOT / args.certificate
    assert path.parent == ROOT and path.suffix == ".json"
    save(path, certificate)
    save(evidence.parent / "ACCEPTANCE-SUMMARY.json", certificate)
    print(json.dumps({"status": certificate["status"], "targets": len(summaries), "counts": final["counts"], "evidence": result["evidence"]}))


if __name__ == "__main__":
    main()
