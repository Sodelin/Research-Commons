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
    assert len(closure) == 121 and all(t['closure_modules'] == 117 for t in summaries.values())
    assert final['counts'] == {'cache_reuse': 116, 'fresh_components': 1}
    proposal_path = ROOT / 'proposals/reuse-integration-20261010T2138Z/parallel-arm-transport/PROPOSAL-FREEZE.json'
    assert sha(proposal_path) == '73e28655aa7277e838c37bf84e56bfe275e5fc592ddc137baa6ce66c99cdb24b'
    proposal = json.loads(proposal_path.read_bytes())
    assert proposal['source']['sha256'] == 'f40a0d66db43984f05ca250dc1d4e9e79372141a498732414d8acde11162d6dc'
    accepted = proposal['accepted_provider_context']
    repo = ROOT.parents[2]
    design = repo / 'research/2026-10-10-codex-lean-rust-parity/design/history/g6-parallel-arm-static-qc-20261010T2322Z-solver_design_recovery/G6-PARALLEL-ARM-STATIC-QC-ATTEMPT1.json'
    plan_acceptance = repo / 'research/2026-10-10-codex-lean-rust-parity/quality/G6-PARALLEL-ARM-117-RUN-PLAN-ACCEPTANCE-20261010T2323Z.json'
    assert sha(design) == '6ddf8390f415959662aab867e26a5593b9fa39f8f5d7e08fca0a7dcfad03cb62'
    assert sha(plan_acceptance) == '0d6e8af9bb83f03de33d9e6dc446b80b6c0a9997974acc08cc73b1b8533cc9a5'
    post = work / ('POST-RUN-TRANSPORT-REHASH-' + Path(result['actual_run']).name + '.json')
    transport = json.loads(post.read_bytes())
    assert transport['status'] == 'PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION'
    assert transport['final_receipt_sha256'] == sha(Path(result['actual_run']) / 'FINAL-RECEIPT.json')
    certificate.update(
        executable_target_modules=117,
        guard_complete_staging_graph_modules=121,
        protected_provider_context_executed=False,
        protected_provider_source_pins={r['module']: r['sha256'] for r in closure if r['module'].startswith('Mathlib.')},
        parent1504_certificate={'path': str(repo / accepted['certificate']), 'sha256': accepted['certificate_sha256']},
        parent1504_independent_QC={'path': str(repo / accepted['root_qc']), 'sha256': accepted['root_qc_sha256']},
        pre_use_source_static_QC={'path': str(design), 'sha256': sha(design)},
        root_run_plan_acceptance={'path': str(plan_acceptance), 'sha256': sha(plan_acceptance)},
        root_source_pin=proposal['source']['sha256'],
        root_independent_saved_review_pending=True,
        scope='Actual original NonrootBigon two parallel-parent occurrence transport at an admitted entering Code whose every live owner is the hybrid. Identity vertex and Copy maps, exchanged two original parent IDs, source network equality, unchanged register values, ancestral rate and all other rates. Pulse route b with bank r has the full original forest/register epoch law of route !b with the transported bank; exact forest and rooted-unranked-forest/register pushforwards inherit that identity. No fixed-Code natural Bernoulli mixture, no-read factorization, source extractor, native/DTO representation or full G6/master closure is claimed. Accepted1504 is not widened by this separate117-root certificate.',
        precise_scope=proposal['precise_scope'],
        remaining_factorization_interface=proposal['remaining_factorization_interface'],
        freshness_qualification='116 exact accepted parent components reused; one new source fresh kernel check plus fresh aggregate and complete117-module owned audit. Four additional protected Mathlib provider records are staging guards and are neither executed as a target nor added to owned counts.',
        post_run_transport_verification={'path': str(post), 'sha256': sha(post), 'status': transport['status']},
        preserved_result={'path': str(result_path), 'sha256': sha(result_path)},
        packet_distribution_complete=result['packet_distribution_complete'],
        full_1504_owned_metadata_retention_claimed=False,
        parent_owned_metadata_qualification='This narrow audit establishes its complete selected117 closure. Parent exact source/object/receipt/import identities are reauthenticated; narrow-context generated ownership/alias records are not silently asserted identical to the full1504 audit. Any such differences are qualified in the later saved review.',
        coherent_union1506_executed=False,
        summarizer_sha256=sha(Path(__file__)))
    path = ROOT / args.certificate
    assert path.parent == ROOT and path.suffix == ".json"
    assert not path.exists()
    save(path, certificate)
    assert not (evidence.parent / "ACCEPTANCE-SUMMARY.json").exists()
    save(evidence.parent / "ACCEPTANCE-SUMMARY.json", certificate)
    print(json.dumps({"status": certificate["status"], "targets": len(summaries), "counts": final["counts"], "evidence": result["evidence"]}))


if __name__ == "__main__":
    main()
