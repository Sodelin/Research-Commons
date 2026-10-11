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
    assert len(fresh) == 1 and len(closure) == 104
    assert all(t['closure_modules'] == 101 for t in summaries.values())
    assert sum(final['counts'].values()) == 101
    proposal_binding = preparation['scratch_location_derivation']['source_freeze']
    proposal_path = Path(proposal_binding['path'])
    assert sha(proposal_path) == proposal_binding['sha256']
    proposal = json.loads(proposal_path.read_bytes())
    assert proposal['graph']['exact_accepted_parent_modules'] == 100
    assert {proposal['module']: proposal['source']['sha256']} == {n: r['sha256'] for n, r in fresh.items()}
    assert len([r for r in closure if r['module'] == 'Mathlib.Analysis.Convex.Caratheodory']) == 1
    accepted_bindings = [
        {'path': str(ROOT / 'HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json'),
         'sha256': '1f45babae7a183dc1638ebfd7de210fddcf2dd872e8498f3f80ede4d06e9fcc2'},
        {'path': str(ROOT.parent / 'quality/HISTORY-SURVIVAL-UNION-1504-REVIEW-20261010T224327.307430Z.json'),
         'sha256': 'e10e65a37003efcd1c9dce3d7cb80a154b034f66bb8dd740ee061f9e35bc33cb'}]
    for binding in accepted_bindings:
        assert sha(Path(binding['path'])) == binding['sha256']
    post = work / ('POST-RUN-TRANSPORT-REHASH-' + Path(result['actual_run']).name + '.json')
    transport = json.loads(post.read_bytes())
    assert transport['status'] == 'PASS_POST_RUN_OLD_ALIASES_AND_NEW_COMPONENT_AUTHENTICATION'
    assert transport['final_receipt_sha256'] == sha(Path(result['actual_run']) / 'FINAL-RECEIPT.json')
    assert transport['live_capture_count'] >= 2
    runtime_parent = preparation['runtime_parent_derivation']
    assert sha(Path(runtime_parent['path'])) == runtime_parent['sha256']
    certificate = {
        'status': 'PASS_COMPLETE_OWNED_AUDITS_FOR_SEPARATE_NEW_PROOF_ROOTS',
        'workspace': str(work), 'actual_run': result['actual_run'], 'evidence': result['evidence'],
        'preservation_manifest_sha256': sha(evidence / 'PRESERVATION-MANIFEST.json'),
        'preserved_result': {'path': str(result_path), 'sha256': sha(result_path)},
        'preparation_sha256': sha(work / 'PREPARATION.json'), 'graph_sha256': final['graph_sha256'],
        'source_pins': preparation['source_pins'], 'fresh_source_versions': fresh,
        'derivatives': preparation['scratch_location_derivation'],
        'contexts': preparation['contexts'], 'targets': summaries, 'counts': final['counts'],
        'kernel_checking': True, 'trust_level': 0, 'compiler_sha256': final['compiler_sha256'],
        'native_runtime_digest': final['native_runtime_digest'], 'compiler_and_native_final_stable': True,
        'executable_target_modules': 101, 'guard_complete_staging_graph_modules': 104,
        'protected_provider_context_executed': False,
        'protected_provider_source_pins': {r['module']: r['sha256'] for r in closure if r['module'].startswith('Mathlib.')},
        'source_freeze': proposal_binding, 'accepted_parent_context_bindings': accepted_bindings,
        'source_provider_partition': {'accepted1504': 100, 'new_source_versions': 1, 'Caratheodory_already_in_executable_closure': True, 'guard_only_records': 3},
        'post_run_transport_verification': {'path': str(post), 'sha256': sha(post), 'status': transport['status']},
        'actual_parent_wrapper_equivalence': runtime_parent,
        'compressed_stderr_qualification': 'The reviewed live logging/cache derivative retains strict compiler flags, caps and kernel/source/import/native/audit gates. Complete combined glibc loader and Lean diagnostic stderr is losslessly gzip-preserved and decoded for native/sorryAx checks. Original separated raw loader receipts remain unchanged.',
        'scope': 'Separate full-Code finite fibre pushforward of accepted positive generator compression and the rational certificate to the complete original register and rooted labelled unranked forest. All-copy CoLocated and liveCard <= M remain explicit; only finite Code fibres are summed. No ambient forest Fintype, new count/coefficient engine, biological positive-factor realization, exterior-panel/future/bin source reconstruction, timed or native representation, extractor, policy/QE or full G6/master closure is claimed. Accepted1504 remains unchanged.',
        'related_owned_obligation_ids': proposal['owned_obligation_ids'], 'proof_role': proposal['proof_role'],
        'source_scope_qualifications': proposal['source_scope'], 'master_closed': False,
        'freshness_qualification': 'Actual component counts and exact receipts distinguish authenticated reuse and fresh checks. The aggregate and complete101-module owned audit are fresh. Three additional protected Mathlib records are staged namespace guards; Caratheodory is already executed in101 and are not executed targets or owned counts.',
        'packet_distribution_complete': result['packet_distribution_complete'],
        'full_1504_owned_metadata_retention_claimed': False,
        'parent_owned_metadata_qualification': 'Only the exact selected101 closure is audited here. Inherited source/object/import/receipt identities are reauthenticated; generated owner labels/private aliases may depend on the narrow context and must be explicitly qualified in saved review.',
        'root_independent_saved_review_pending': True,
        'historical_evidence_or_scientific_gates_promoted': False,
        'coherent_union_executed': False, 'summarizer_sha256': sha(Path(__file__)),
        'parent_summarizer_sha256': '9e5cc6c4c0c559ea305b85edf1ae45f250742bc7edf9250673b5b782a55b3f71',
        'summarizer_derivation': 'Same strict result/distributed raw-byte/source/aggregate/owned/native/transport checks; adapt only forest proposal schema,101/104/100-parent1-source counts, scope and immutable1504 acceptance bindings.'}
    path = ROOT / args.certificate
    assert path.parent == ROOT and path.suffix == '.json' and not path.exists()
    save(path, certificate)
    summary = evidence.parent / 'ACCEPTANCE-SUMMARY.json'
    assert not summary.exists()
    save(summary, certificate)
    print(json.dumps({'status': certificate['status'], 'targets': summaries, 'counts': final['counts'], 'evidence': result['evidence']}))


if __name__ == '__main__':
    main()
