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
    fresh = json.loads((work / 'FRESH-SOURCES.json').read_bytes())
    closure = json.loads((work / 'SOURCE-CLOSURE.json').read_bytes())
    assert len(fresh) == 2 and len(closure) == 145
    assert all(t['closure_modules'] == 141 for t in summaries.values())
    assert sum(final['counts'].values()) == 141
    proposal_binding = preparation['scratch_location_derivation']['source_freeze']
    proposal_path = Path(proposal_binding['path'])
    assert sha(proposal_path) == proposal_binding['sha256']
    proposal = json.loads(proposal_path.read_bytes())
    assert proposal['exact_composition']['accepted_parent_count'] == 139
    assert {r['module']: r['sha256'] for r in proposal['sources']} == {n: r['sha256'] for n, r in fresh.items()}
    repo = ROOT.parents[2]
    for binding in proposal['acceptance_bindings']:
        assert sha(repo / binding['path']) == binding['sha256']
    post = work / ('POST-RUN-TRANSPORT-REHASH-' + Path(result['actual_run']).name + '.json')
    transport = json.loads(post.read_bytes())
    assert transport['status'] == 'PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION'
    assert transport['final_receipt_sha256'] == sha(Path(result['actual_run']) / 'FINAL-RECEIPT.json')
    assert transport['live_capture_count'] >= 2
    runtime_parent = preparation['runtime_parent_derivation']
    assert sha(Path(runtime_parent['path'])) == runtime_parent['sha256']
    partial_binding = preparation['scratch_location_derivation']['source_partition']['partial_component_provenance']
    assert sha(Path(partial_binding['path'])) == partial_binding['sha256']
    partial = json.loads(Path(partial_binding['path']).read_bytes())
    assert partial['status'] == 'PASS_KERNEL_COMPONENT_AUTHENTICATION_ONLY_TARGET_INCOMPLETE'
    assert partial['module'] == 'G6OriginalCommonPrefix'
    assert partial['source_sha256'] == fresh[partial['module']]['sha256']
    assert not partial['root_or_audit_accepted']
    assert sha(work / 'PARTIAL-COMPONENT-ADMISSION-PROVENANCE.json') == partial_binding['sha256']
    for binding in preparation['scratch_location_derivation']['source_repair_derivation']['partial_component_gate_bindings']:
        assert sha(Path(binding['path'])) == binding['sha256']
    certificate = {
        'status': 'PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS',
        'workspace': str(work), 'actual_run': result['actual_run'], 'evidence': result['evidence'],
        'preservation_manifest_sha256': sha(evidence / 'PRESERVATION-MANIFEST.json'),
        'preserved_result': {'path': str(result_path), 'sha256': sha(result_path)},
        'preparation_sha256': sha(work / 'PREPARATION.json'), 'graph_sha256': final['graph_sha256'],
        'source_pins': preparation['source_pins'], 'fresh_source_versions': fresh,
        'derivatives': preparation['scratch_location_derivation'],
        'contexts': preparation['contexts'], 'targets': summaries, 'counts': final['counts'],
        'partial_prefix_component_only_provenance': partial_binding,
        'source_versions_distinct_from_invocation_freshness': {'new_source_versions': 2, 'qualified_partial_prefix_components': 1, 'pending_factorization_fresh_checks': 1},
        'kernel_checking': True, 'trust_level': 0, 'compiler_sha256': final['compiler_sha256'],
        'native_runtime_digest': final['native_runtime_digest'], 'compiler_and_native_final_stable': True,
        'executable_target_modules': 141, 'guard_complete_staging_graph_modules': 145,
        'protected_provider_context_executed': False,
        'protected_provider_source_pins': {r['module']: r['sha256'] for r in closure if r['module'].startswith('Mathlib.')},
        'source_freeze': proposal_binding, 'accepted_parent_context_bindings': proposal['acceptance_bindings'],
        'source_provider_partition': {'accepted1504': 138, 'separately_accepted_parallel_arm': 1, 'new_source_versions': 2},
        'post_run_transport_verification': {'path': str(post), 'sha256': sha(post), 'status': transport['status']},
        'actual_parent_wrapper_equivalence': runtime_parent,
        'compressed_stderr_qualification': 'The reviewed live logging/cache derivative retains strict compiler flags, caps and kernel/source/import/native/audit gates. Complete combined glibc loader and Lean diagnostic stderr is losslessly gzip-preserved and decoded for native/sorryAx checks. Original separated raw loader receipts remain unchanged.',
        'scope': 'Separate natural COMMON full-forest/register factorization over the exact original parallel-arm, seed/history, exposure, no-read and tied-prefix assumptions in the frozen theorem statements. All raw providers and initialization are inherited; no supplied family/source/graph reconstruction, timed observer refinement, native representation, DTO extractor, global policy/QE or full G6/master closure is claimed. Accepted1504 remains unchanged.',
        'discharges': proposal['discharges'], 'remaining_interfaces': proposal['remaining_interfaces'],
        'freshness_qualification': 'Actual component counts and exact receipts distinguish authenticated reuse and fresh checks. The aggregate and complete141-module owned audit are fresh. Four additional protected Mathlib records are staged namespace guards and are not executed targets or owned counts.',
        'packet_distribution_complete': result['packet_distribution_complete'],
        'full_1504_owned_metadata_retention_claimed': False,
        'parent_owned_metadata_qualification': 'Only the exact selected141 closure is audited here. Inherited source/object/import/receipt identities are reauthenticated; generated owner labels/private aliases may depend on the narrow context and must be explicitly qualified in saved review.',
        'root_independent_saved_review_pending': True,
        'historical_evidence_or_scientific_gates_promoted': False,
        'coherent_union_executed': False, 'summarizer_sha256': sha(Path(__file__)),
        'parent_summarizer_sha256': '9e5cc6c4c0c559ea305b85edf1ae45f250742bc7edf9250673b5b782a55b3f71',
        'summarizer_v2_derivation': 'Only explicitly authenticate and distinguish the authorized unchangedprefix component from139 accepted parent-root providers and the newfactorization; original strict complete141audit/count/native/source/result/transport gates retained.'}
    path = ROOT / args.certificate
    assert path.parent == ROOT and path.suffix == '.json' and not path.exists()
    save(path, certificate)
    summary = evidence.parent / 'ACCEPTANCE-SUMMARY.json'
    assert not summary.exists()
    save(summary, certificate)
    print(json.dumps({'status': certificate['status'], 'targets': summaries, 'counts': final['counts'],
        'partial_prefix_component_only_provenance': partial_binding,
        'source_versions_distinct_from_invocation_freshness': {'new_source_versions': 2, 'qualified_partial_prefix_components': 1, 'pending_factorization_fresh_checks': 1}, 'evidence': result['evidence']}))


if __name__ == '__main__':
    main()
