#!/usr/bin/env python3
"""Read-only historical context and additive G3 owner audit; never invokes Lean.

Contributor: Codex / lean_integration_successor, 10 October 2026.
Writes only uniquely dated audit outputs. All accepted graphs, source stores,
compiler artifacts, receipts and prior audits remain unchanged.
"""
import collections
import datetime
import gzip
import hashlib
import json
import pathlib
import re
import shutil

LEAN = pathlib.Path(__file__).resolve().parents[1]
PACKET = LEAN.parent
REPO = PACKET.parents[1]
WORK = pathlib.Path('/dev/shm/rc-lean-history-accepted-union-1497-20261010T204542.182773Z')
DOT = REPO / 'research/2026-10-10-dot-modular-lean-reuse-handoff-1448z/g3-fixed-residue-critical-bridge-1522z'


def read(path):
    return json.loads(path.read_bytes())


def pin(path):
    return {'path': str(path), 'sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
            'bytes': path.stat().st_size}


def compare_scope(scope, selected):
    missing = {m: r['sha256'] for m, r in scope['modules'].items() if m not in selected}
    conflicts = {m: {'historical_sha256': r['sha256'], 'current_sha256': selected[m]['sha256'],
                     'literal_imports_equal': r['imports'] == selected[m]['imports']}
                 for m, r in scope['modules'].items() if m in selected and
                 (r['sha256'], r['imports']) != (selected[m]['sha256'], selected[m]['imports'])}
    return {'modules': len(scope['modules']), 'roots': scope['roots'],
            'exact_source_and_literal_import_subset': not missing and not conflicts,
            'missing_modules': missing, 'source_or_import_variants': conflicts}


def unique_allocation(paths):
    seen = set()
    allocated = logical = files = 0
    for root in paths:
        candidates = root.rglob('*') if root.is_dir() else [root]
        for p in candidates:
            if p.is_symlink() or not p.is_file():
                continue
            s = p.stat()
            key = (s.st_dev, s.st_ino)
            if key in seen:
                continue
            seen.add(key)
            allocated += s.st_blocks * 512
            logical += s.st_size
            files += 1
    return {'allocated_bytes': allocated, 'logical_bytes': logical, 'distinct_inode_files': files}


def canonical(row):
    return {k: sorted(v) if isinstance(v, list) else v for k, v in row.items()}


def main():
    now = datetime.datetime.now(datetime.timezone.utc)
    stamp = now.strftime('%Y%m%dT%H%M%S.%fZ')
    selected = read(WORK / 'DEPENDENCY-GRAPH.json')['targets']['current/connected']['modules']
    certificate = read(LEAN / 'HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json')
    qr = PACKET / 'quality/HISTORY-ACCEPTED-UNION-1497-REVIEW.json'
    qi = PACKET / 'quality/HISTORY-UNION-INVENTORY-REVIEW.json'
    assert read(qr)['pass'] and read(qi)['pass']
    assert len(selected) == 1497

    published_certificate = read(LEAN / 'PUBLISHED53-CERTIFICATE.json')
    published_work = pathlib.Path(published_certificate['workspace'])
    published = read(published_work / 'DEPENDENCY-GRAPH.json')['targets']
    required = {r['target']: r for r in published_certificate['profile_results']}
    public_coverage = {}
    for label, scope in published.items():
        public_coverage[label] = {
            **compare_scope(scope, selected), 'required_profile': label in required,
            'original_result': required.get(label, {}).get('status'),
            'prior_status': scope.get('prior_status'),
            'required_for_accepted_release': scope.get('required_for_accepted_release', label in required)}
    reference = {label: compare_scope(scope, selected)
                 for label, scope in read(LEAN / 'DEPENDENCY-GRAPH.json')['targets'].items()}
    assert len(required) == 53 and len(published) == 78
    assert sum(r['exact_source_and_literal_import_subset'] for k, r in public_coverage.items()
               if k in required) == 49
    assert len(reference) == 52 and sum(r['exact_source_and_literal_import_subset']
                                      for r in reference.values()) == 49
    provisional = {k: v for k, v in public_coverage.items() if k not in required}
    assert len(provisional) == 25 and all(v['prior_status'] ==
        'INDEPENDENT_SOURCE_ACCEPTANCE_ONLY_COMPILER_UNCHECKED' for v in provisional.values())

    historical_certificates = {}
    for f in sorted(LEAN.glob('*CERTIFICATE.json')):
        if f.name == 'HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json':
            continue
        d = read(f)
        record = {'certificate': pin(f), 'status': d.get('status'),
                  'workspace': d.get('workspace'), 'accepted_target_coverage': {}}
        if d.get('workspace') and isinstance(d.get('targets'), dict):
            graph_path = pathlib.Path(d['workspace']) / 'DEPENDENCY-GRAPH.json'
            if graph_path.exists():
                graph = read(graph_path)['targets']
                record['graph'] = pin(graph_path)
                for label, target in d['targets'].items():
                    if str(target.get('status', '')).startswith('PASS') and label in graph:
                        record['accepted_target_coverage'][label] = compare_scope(graph[label], selected)
            else:
                record['saved_context_graph_available'] = False
        record['source_pin_variants'] = {m: {'historical': h, 'current': selected[m]['sha256']}
            for m, h in d.get('source_pins', {}).items() if m in selected and h != selected[m]['sha256']}
        historical_certificates[f.name] = record
    assert len(historical_certificates) == 48

    variants = []
    for module, old_hash, new_hash, normalization in [
        ('FeedbackDynamics', 'dd14dcaf5da5e89ff4aa9a2afb0693bb95a40642c6030287860a14f982f2d570',
         '0e8ac4ce157b5c3d8a66eb5d9ebe6ced7c1adbccf10359f1894fe4e72fc0a15a', 'CRLF'),
        ('SourceLabelledForest', '5a0f070216bc6564f0f23b3cd283be27722eb7582eb77c67a16c6c5fffa4e4aa',
         'd6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d', 'final_blank_line')]:
        old = published_work / 'source-store' / (old_hash + '.lean')
        new = WORK / 'source-store' / (new_hash + '.lean')
        assert pin(old)['sha256'] == old_hash and pin(new)['sha256'] == new_hash
        a, b = old.read_bytes(), new.read_bytes()
        equal = a.replace(b'\r\n', b'\n') == b.replace(b'\r\n', b'\n') if normalization == 'CRLF' else a.rstrip(b'\n') == b.rstrip(b'\n')
        assert equal
        variants.append({'module': module, 'old': pin(old), 'current': pin(new),
                         'normalization_checked': normalization, 'normalized_complete_bytes_equal': equal,
                         'byte_contexts_remain_distinct': True})
    nanuq_old = published_work / 'source-store/4eb5913c634bffb05132738a21fb4396f6b93d99b8a2b4073c8387549788f00c.lean'
    nanuq_new = WORK / 'source-store/fc9e375ef550d737a7a2aa3789bc9b399c074e518402ff12c9da60e844811ce5.lean'
    curves = WORK / 'source-store/a9689b698a689f0f318af2fd25539e50fd60fb1643da70f50265c55459d2c108.lean'
    heads = ['Plane', 'PlanarCurves', 'drawing', 'TaxonOuterFace', 'OuterLabelledCurves',
             'actual_outer_face_of_drawing_subset', 'actual_three_path_trace_is_old_union']
    assert all(re.search(r'\b' + h + r'\b', curves.read_text()) for h in heads)
    variants.append({'module': 'NanuqInterface', 'old': pin(nanuq_old), 'current_import_only': pin(nanuq_new),
                     'current_reexport_provider': pin(curves), 'seven_prior_exported_heads_found': heads,
                     'qualification': 'Distinct source contexts; current import-only interface resolves duplicate global geometry names by reexporting the accepted G1 curve provider.'})

    endpoints = [
        ('G1FullOriginalClassMasterAndSharpness', 'Original admitted CutChild Source with HasGalledOuterSemidirectedPartner, n>=4: derived same-source normalized root interface, 2n-2 / 6n-5 / 8n-8 bounds and exact saturators; graph size is not a G3 physical word-length bound.'),
        ('UnifiedLean.Source.ControlledUnrankedSourceProjectivity', 'Actual controlled original unranked all-panel projectivity; same original register, rather than resampled hybrid choices.'),
        ('UnifiedLean.Source.SourceUnrankedCopyProjectivity', 'Actual natural original-copy projectivity, including small/empty carriers at its source premises.'),
        ('G2FaithfulTimedOutput', 'actual_original_faithful_output derives pair certificate, ancestral roots and faithful timed output from the actual complete calendar trace; its final original-source theorem discharges the generic identity-certificate premise.'),
        ('G2ActualTimedAllPanelLaw', 'Actual timed pruning and controlled/natural all-panel laws, including empty/singleton panels, with the original once-drawn register.'),
        ('G2AssembledBoundaryNull', 'Actual calendar and ancestral-tail active grafts almost surely avoid every fixed original date; finite fibres and segment maps are derived, rather than assuming boundary nullity.'),
        ('G5M3NormalizedClusterSplitIdentification', 'Documented M3 upper endpoint: two positive-rate/interior original cut-child sources with common contemporary tip age and >=3 taxa; equal ordinary Fin3 injective tip-panel laws identify full normalized-cluster and nontrivial unordered-split unions.'),
        ('G6ActualCellObservedTV', 'Actual completed finite-bin TV in one same calendar/cut cell and one fixed reader/shared bank is bounded by derived rational Lipschitz constant times physical-bank distance; no independent-variable admission replaces the source law.'),
        ('GeneratedCompleteBinProxy', 'Constructs an actual cut word for any supplied finite list and derives proxy TV under explicit rate/inheritance/Budget bounds; this does not construct the global unknown-source effective cover.'),
        ('G6OriginalPopulationGeneratorBounds', 'Original full-Code population row coarse generator remainder, live cap M rather than Code-cardinality multiplier, ordered-pair 1/2 and Q=-P\'(1); row-L1 and TV-half qualification remain separate.'),
        ('G6PositiveGeneratorCompression', 'One positive list of original input atom preimages preserves total mass and tail moments uniformly over every admissible original Code row; existential compression is not an effective extractor.'),
        ('G7ExactLawResourceGame', 'Exact-law response histories use one admitted source across all rows; finite Winning recursion iff valid plan. Losing gives same-full-history witnesses, not one fixed pair defeating every policy.'),
        ('G7ActualExactLawResponses', 'Actual controlled completed unranked readout polynomial from the original physical calendar, with same-order charts, positive rates, interior inheritance and original shared IDs/modes; offsets, coefficients and legality are explicit inputs.'),
        ('G7ExactLawRankCompression', 'Affine pointwise-total policies admit finite informative horizon bounded by finrank, under deletion legality and same-history consistency; no effective span test or CAD implementation is supplied.'),
        ('G7OriginalFamilyStrategy', 'Actual finite RootedBinary/strict-calendar family with all original hybrid IDs, positive rates and interior inheritance. Positive-weight original rows/sites/calls are charged. Arbitrary admitted predicate and Allowed programmes remain inputs; classical plans are not a runtime policy producer.'),
        ('G7OriginalCarrierCoverage', 'Arbitrary finite original CutChild carrier sources are simultaneously covered by exact-ID relabelling and inherited V/E census, preserving complete same-ID laws; outer-labelled planarity and algebraic parameter admissions remain separate.'),
        ('G7OriginalEdgeOperators', 'Exact full original-Code ordered-pair generator and commuting population operators, preserving original rates.'),
        ('G7OriginalEdgeBoundary', 'Exact safe node/other-population and other-edge exit commutations; no arbitrary phase-slot permutation is asserted.'),
        ('G7OriginalEdgeGathering', 'gather_entire_word for arbitrary finite original interval/exit/node event list, without a desired-kernel equality premise; residual bank absorption is per register realization.'),
        ('G7ActualCalendarGathering', 'Generated original sorted-date/Finset.toList calendar equals its original physical matrix and natural once-register gathering law; exposure telescope and unrelated downstream claims remain separate.'),
        ('G7OriginalCompletionFixture', 'Original completion fixture library is compatible; its global Main and accepted six-case/257-view actual evaluation remain in the separate original execution context.'),
        ('UnifiedLean.G3.ConditionalZeroScoreConsumer', 'WholeFibreProvider assumes core/piece coverage, actual source certificate/faithfulness and length/numeric identities. The conditional consumer does not construct whole-source finite coverage or terminating exact G3 decision.'),
        ('G4TwoRootSourceStopping', 'Observable finite-length certificate assumes an antitone all-rival envelope tending to zero; this is the scoped contraction/upper-bound branch, not a general unknown-size closure theorem.')]
    body_scopes = []
    for module, scope in endpoints:
        assert module in selected, module
        f = WORK / 'source-store' / (selected[module]['sha256'] + '.lean')
        assert pin(f)['sha256'] == selected[module]['sha256']
        body_scopes.append({'module': module, 'source': pin(f), 'literal_imports': selected[module]['imports'],
                            'actual_body_and_premise_scope': scope})

    manifest = read(DOT / 'SOURCE-MANIFEST.json')
    additive = read(DOT / 'ADDITIVE-PROFILE.json')
    scope = additive['source_scope']
    shared, new, source_pins = {}, {}, {}
    for row in manifest['modules']:
        m, h = row['module'], row['sha256']
        f = DOT / 'source-store' / (h + '.lean') if row['new_source'] else WORK / 'source-store' / (h + '.lean')
        assert pin(f)['sha256'] == h and f.stat().st_size == row['bytes']
        literal = [s for line in re.findall(r'^import\s+([^\r\n]+)', f.read_text(), re.M) for s in line.split()]
        assert literal == row['imports'] == scope['modules'][m]['imports']
        source_pins[m] = {'source': pin(f), 'imports': literal, 'new_source': row['new_source']}
        if m in selected:
            assert (h, literal) == (selected[m]['sha256'], selected[m]['imports'])
            shared[m] = h
        else:
            new[m] = h
    assert len(shared) == 6 and len(new) == 64
    assert not scope['unresolved_imports']

    cache_dirs = [LEAN / '.build/cache', WORK / '.build/cache']
    cache_dirs += list((LEAN / '.build/proof-extensions').glob('*/*/.build/cache'))
    cache_dirs += list(pathlib.Path('/tmp').glob('rc-lean-*/.build/cache'))
    cache_seen, matching, receipt_count = set(), collections.defaultdict(list), 0
    for d in cache_dirs:
        for f in d.glob('*/receipt.json'):
            s = f.stat()
            key = (s.st_dev, s.st_ino)
            if key in cache_seen:
                continue
            cache_seen.add(key)
            receipt_count += 1
            r = read(f)
            if new.get(r['module']) == r.get('source_sha256'):
                matching[r['module']].append(pin(f))
    assert not matching
    delivered_objects = [str(f) for f in DOT.rglob('*') if f.is_file() and
                         (f.suffix in ['.olean', '.ilean', '.ir'] or f.name.endswith(('.olean.private', '.olean.server')))]
    assert not delivered_objects
    raw_audit_path = pathlib.Path(certificate['actual_run']) / 'attempts/00002-OwnedAudit/work/AUDIT-RESULT.json'
    assert pin(raw_audit_path)['sha256'] == certificate['targets']['current/connected']['audit_raw_sha256']
    old_audit = read(raw_audit_path)
    new_audit = read(DOT / 'evidence/AUDIT-RESULT.json')
    old_names = {r['name']: r for r in old_audit['declarations']}
    shared_rows = [r for r in new_audit['declarations'] if r['module'] in shared]
    shared_metadata_differences = [r['name'] for r in shared_rows
        if r['name'] not in old_names or canonical(r) != canonical(old_names[r['name']])]
    incompatible_names = [r['name'] for r in new_audit['declarations']
        if r['module'] in new and r['name'] in old_names]
    target_row = next(r for r in new_audit['declarations'] if r['name'] ==
        'GProgram.G3.CriticalCertificates.actual_fixed_residue_strict_critical_finite')
    result = read(DOT / 'evidence/RESULT.json')
    external_native = result['component_receipts'][0]['native_runtime_digest']
    local_native = certificate['native_runtime_digest']
    assert external_native != local_native
    assert not new_audit['owned_axioms'] and not new_audit['nonstandard_axiom_rows'] and not new_audit['missing_modules']

    allocation = unique_allocation([WORK])
    export_path = LEAN / certificate['evidence']
    exports = unique_allocation([export_path])
    cap = 1 << 30
    new_sources_rounded = sum(((source_pins[m]['source']['bytes'] + 4095) // 4096) * 4096 for m in new)
    owner = {
        'schema': 'g3_additive_profile_static_owner_handoff_v1',
        'status': 'CHECKED_EXTERNAL_SOURCE_PROFILE_COMPATIBLE_BUT_NEW_LOCAL_RUN_NOT_BUDGET_CERTIFIED',
        'observed_utc': now.isoformat(), 'contributor': 'Codex / lean_integration_successor',
        'source_manifest': pin(DOT / 'SOURCE-MANIFEST.json'), 'additive_profile': pin(DOT / 'ADDITIVE-PROFILE.json'),
        'public_projection_policy': pin(DOT / 'PROJECTION-POLICY.json'),
        'public_result': pin(DOT / 'evidence/RESULT.json'), 'complete_exact_public_audit': pin(DOT / 'evidence/AUDIT-RESULT.json'),
        'external_target': additive['profile'], 'external_profile_graph_sha256': additive['graph_sha256'],
        'sources': source_pins, 'matched_existing_six': shared, 'new_bodies_64': new,
        'source_and_literal_import_conflicts': [], 'prospective_union_modules': len(selected) + len(new),
        'new_selected_declaration_name_collisions': incompatible_names,
        'shared_owned_metadata_rows_checked': len(shared_rows), 'shared_owned_metadata_differences': shared_metadata_differences,
        'external_selected_modules': 70, 'external_fresh_components_in_final_run': 9,
        'external_authenticated_reused_components_in_final_run': 61,
        'external_owned_declarations': new_audit['declaration_count'],
        'external_theorem_declarations': new_audit['theorem_declaration_count'],
        'external_owned_axioms': [], 'external_nonstandard_axiom_rows': [], 'external_missing_modules': [],
        'external_endpoint_owned_audit_row': target_row,
        'external_raw_result_sha256': read(DOT / 'PUBLICATION-MANIFEST.json')['raw_result_sha256'],
        'local_cache_directories_scanned': len(cache_dirs), 'distinct_local_cache_receipts_scanned': receipt_count,
        'matching_new64_local_cache_receipts': dict(matching), 'distributed_compiled_object_files': delivered_objects,
        'external_native_runtime_digest': external_native, 'local_native_runtime_digest': local_native,
        'external_receipt_admitted_as_local_cache': False,
        'allocation': {'existing1497_scratch_distinct_inode': allocation, 'existing1497_packet_exports': exports,
            'total_new_scratch_cap_bytes': cap, 'remaining_scratch_bytes_before_new70': cap - allocation['allocated_bytes'],
            'remaining_after_existing_exports_if_also_charged': cap - allocation['allocated_bytes'] - exports['allocated_bytes'],
            'new64_source_logical_bytes': sum(source_pins[m]['source']['bytes'] for m in new),
            'new64_source_rounded_bytes': new_sources_rounded,
            'new64_compiler_output_bundle_bytes': None,
            'reason_output_bytes_unknown': 'Objects/companions are not delivered and projected receipts provide their hashes without byte sizes. No matching local artifacts exist.',
            'external_observed_path_counted_peak_bytes': read(DOT / 'evidence/SUPERVISOR-RECEIPT.json')['peak_observed_allocated_bytes'],
            'external_peak_is_not_a_local_remaining_allocation_bound': True,
            'conservative_fresh_coherent_aggregate_audit_reserve_bytes': 256 << 20,
            'full_new_union_remaining_before_64_outputs_or_metadata': cap - allocation['allocated_bytes'] - new_sources_rounded - (256 << 20),
            'current_available_bytes': {str(x): shutil.disk_usage(x).free for x in [LEAN, pathlib.Path('/tmp'), pathlib.Path('/dev/shm')]},
            'new_profile_materialized': False, 'compiler_started': False},
        'owner_action': 'Preserve this additive target as a separately checked external exact-source profile. Do not add it to the accepted1497 graph or promote external9abb receipts into local6f8 caches. A later local recheck requires a measured component-output/export budget or revised storage authorization; existing mathematical sources/core/flags/caps stay unchanged.',
        'mathematical_scope': 'For every real r>0, the strict pairs 0<p,q<1 solving both supplied original Bernoulli weighted response equations for normalWeight r on exponents1,3,6,10,15,21 form a finite set. Final theorem has no certificate/algebraicity premise. It does not acquire the normal, enumerate transcendental solutions, bound repeated source occurrences, construct a whole-fibre source witness, or decide G3.',
        'accepted1497_modified': False, 'new_target_or_aggregate_accepted_locally': False,
        'compiler_evaluator_or_native_process_invoked': False, 'auditor': pin(pathlib.Path(__file__))}
    owner_path = LEAN / ('HISTORY-CONTEXT-COVERAGE-AUDIT-G3-OWNER-' + stamp + '.json')
    assert not owner_path.exists()
    owner_path.write_text(json.dumps(owner, indent=2) + '\n')

    report = {
        'schema': 'historical_context_coverage_audit_v1',
        'status': 'PASS_EXPLICIT_READONLY_HISTORICAL_COVERAGE_AND_BODY_SCOPE_AUDIT',
        'observed_utc': now.isoformat(), 'contributor': 'Codex / lean_integration_successor',
        'accepted1497_certificate': pin(LEAN / 'HISTORY-ACCEPTED-UNION-1497-CERTIFICATE.json'),
        'accepted1497_root_review': pin(qr), 'accepted1497_inventory_review': pin(qi),
        'accepted1497_final_handoff': pin(LEAN / 'HISTORY-ACCEPTED-UNION-1497-FINAL-HANDOFF.json'),
        'reference52_graph': pin(LEAN / 'DEPENDENCY-GRAPH.json'), 'reference52_explicit_coverage': reference,
        'published53_graph': pin(published_work / 'DEPENDENCY-GRAPH.json'),
        'published53_original_certificate': pin(LEAN / 'PUBLISHED53-CERTIFICATE.json'),
        'published53_explicit_78_profile_coverage': public_coverage,
        'required53_exact_subsets': 49, 'required53_alternate_source_profiles': 4,
        'original53_scope': 'The original52PASS/1FAILED result remains PARTIAL_ORIGINAL_POLICY_REPLAY. The exact337 separate6GiB retry PASS does not rewrite that original run.',
        'separate337_resource_exception': pin(LEAN / 'BASE-RESOURCE-EXCEPTION-CERTIFICATE.json'),
        'all25_provisional_source_only_profiles': provisional,
        'historical48_certificate_explicit_coverage': historical_certificates,
        'preserved_variant_bodies': variants, 'actual_body_and_premise_matches': body_scopes,
        'intentional_exclusions': 'Global Main modules retain separate accepted original evaluator contexts; prior1489 global-main collision remains preserved. Coefficient diagnostic/smoke roots are separately audited diagnostics, not omitted mathematical engines. Every target/module variant and absent module is explicitly recorded above.',
        'recovered_omitted_accepted_roots': read(LEAN / 'HISTORY-ACCEPTED-UNION-1497-FINAL-HANDOFF.json')['parent_certificates_and_ten_additions'],
        'latest_external_g3_owner_handoff': pin(owner_path),
        'objective_library_completeness': 'The1497 coherent library includes the compatible accepted mathematical roots previously omitted from1487 and retains every prior source/import/owned-declaration field. Historical alternate-byte and duplicate-interface profiles, separate executable roots and source-only provisional profiles are explicitly qualified, rather than silently counted as this coherent context.',
        'objective_master_completeness': 'Library acceptance is not blanket G1-G7 master completion. Existing actual timed/projective G2, documented G1 and M3 endpoints, raw-calendar/phase/completion, original-row A/B bounds and finite-horizon semantic policy consumers resolve several older pending entries. Effective whole-fibre source-witness/NO/word-bound G3, general fixed-target unknown-size G4 closure, complete effective source-image/closure G6 assembly and outer-cofacial admission/QE policy extraction G7 remain separate formal/runtime obligations. Earlier hand-reviewed endpoints must not be relabelled mathematically unresolved merely because a producer is absent.',
        'compiler_evaluator_or_native_process_invoked_by_this_audit': False,
        'accepted_sources_helpers_receipts_or_artifacts_mutated': False,
        'auditor': pin(pathlib.Path(__file__))}
    report_path = LEAN / ('HISTORY-CONTEXT-COVERAGE-AUDIT-' + stamp + '.json')
    assert not report_path.exists()
    report_path.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'report': pin(report_path), 'g3_owner_handoff': pin(owner_path),
        'required53_exact': 49, 'provisional_source_only': 25, 'historical_certificates': 48,
        'latest_shared': 6, 'latest_new': 64, 'prospective_modules': 1561,
        'shared_metadata_differences': len(shared_metadata_differences),
        'new_name_collisions': len(incompatible_names), 'budget': owner['allocation']}))


if __name__ == '__main__':
    main()
