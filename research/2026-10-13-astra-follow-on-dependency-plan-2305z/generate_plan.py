#!/usr/bin/env python3
"""Serialize source-only follow-on plans; never invoke Lean, Lake, Git or a build."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SEL = ROOT / 'research/2026-10-13-astra-unified-solver-0645z/intake/SELECTED-LEAN.json'
DELTA = ROOT / 'research/2026-10-13-astra-legal-row-support-2115z/DEPENDENCY-DELTA.json'
ACTIVE = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z/PROVIDER-SELECTION.json'
EXTERNAL = ROOT / 'research/2026-10-13-astra-positive-support-adapter-0830z/EXTERNAL-PLAN.json'
UPSTREAM = ROOT / 'research/2026-10-13-astra-legal-row-support-2115z/UPSTREAM-MATHLIB-AUTH.json'


def read(p):
    return json.loads(p.read_text())


def pin(p):
    b = p.read_bytes()
    return dict(path=str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),
                sha256=hashlib.sha256(b).hexdigest(), bytes=len(b),
                git_blob=hashlib.sha1(b'blob ' + str(len(b)).encode() + bytes([0]) + b).hexdigest())


def uncomments(s):
    """Preserve line boundaries and quoted strings; remove nested Lean comments."""
    out = []; i = 0; depth = 0; quoted = False
    while i < len(s):
        if depth:
            if s.startswith('/-', i): depth += 1; out.extend('  '); i += 2
            elif s.startswith('-/', i): depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
        elif quoted:
            out.append(s[i])
            if s[i] == '\\' and i + 1 < len(s): out.append(s[i+1]); i += 2
            else:
                if s[i] == '"': quoted = False
                i += 1
        elif s.startswith('/-', i): depth = 1; out.extend('  '); i += 2
        elif s.startswith('--', i):
            j = s.find('\n', i)
            if j < 0: j = len(s)
            out.extend(' ' * (j-i)); i = j
        else:
            if s[i] == '"': quoted = True
            out.append(s[i]); i += 1
    assert depth == 0, 'unterminated Lean comment'
    return ''.join(out)


def imports(p):
    out = []
    for line in uncomments(p.read_text()).splitlines():
        m = re.match(r'^\s*(?:(?:public|private|meta)\s+)*import\s+(.+?)\s*$', line)
        if m:
            names = m[1].split()
            assert all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', n) for n in names), (p, line)
            out.extend(names)
    return out


def signature(p, name):
    s = p.read_text()
    m = re.search(r'(?m)^(?:noncomputable\s+)?(?:theorem|lemma|def)\s+' + re.escape(name) + r'\b', s)
    assert m, (p, name)
    e = s.find(':=', m.start())
    assert e > m.start()
    return dict(declaration=name, line=s[:m.start()].count('\n')+1, exact_signature=s[m.start():e].rstrip())


def save(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2) + '\n')


def main():
    selected = read(SEL); delta = read(DELTA); active = read(ACTIVE); ext = read(EXTERNAL)
    graph = read(ROOT / selected['graph_path'])['targets'][selected['selected_target']]
    records = {r['module']:r for r in selected['modules']}
    active_names = {r['module'] for r in active['owned']}
    roots = ['G4WholeProfileDetermination', 'G4ActualSparseCertificateExistence',
             'G2LiteralTimedObservationPruning', 'UnifiedLean.Source.ControlledUnrankedSourceProjectivity']
    seen = set()
    def visit(n):
        if n in seen: return
        seen.add(n)
        for dep in records[n]['imports']:
            if dep in records: visit(dep)
    for n in roots: visit(n)
    assert seen == set(delta['selected_owned_closure']) and len(seen) == 469
    assert active_names <= seen and len(active_names) == 319
    order = [n for n in graph['order'] if n in seen]
    assert len(order) == 469
    official = {r['module']:r for r in ext['modules']}
    owned = []; direct_external = set()
    for n in order:
        r = records[n]; p = ROOT / r['path']; actual = pin(p)
        for field in ['sha256', 'git_blob', 'bytes']: assert actual[field] == r[field], (n, field)
        header = imports(p)
        assert header == r['imports'], (n, header, r['imports'])
        assert graph['modules'][n]['sha256'] == r['sha256']
        direct_external.update(d for d in header if d not in seen)
        owned.append(dict(r, destination=n.replace('.', '/')+'.lean',
                          active_profile_member=n in active_names,
                          imports_from_actual_header=header))
    assert sorted(direct_external) == delta['direct_external_roots']
    upstream = read(UPSTREAM)
    for r in upstream['bodies']:
        local = pin(Path(r['local_upstream_path']))
        for field in ['sha256', 'git_blob', 'bytes']: assert local[field] == r[field]
        assert records[r['module']]['sha256'] == local['sha256']
    external_records = []
    for n in sorted(direct_external):
        if n in official:
            old = official[n]; p = Path(old['source']); actual = pin(p)
            assert actual['sha256'] == old['source_sha256'], n
            external_records.append(dict(module=n, source=actual,
                literal_source_imports=imports(p), current_plan_record=old,
                current_plan_root=n in ext['roots'], reuse_status='source-equal candidate only; object compatibility not inspected'))
        else:
            assert n == 'Lean.Elab.Tactic.Omega', n
            p = Path('/workspace/scratch/astra-lean-0645/lean-4.33.1-linux/src/lean/Lean/Elab/Tactic/Omega.lean')
            external_records.append(dict(module=n, source=pin(p), literal_source_imports=imports(p),
                current_plan_record=None, current_plan_root=False,
                reuse_status='toolchain provider; executable/object identity not rechecked by this plan'))
    staged_paths = [ROOT/r['path'] for r in delta['staged_astra_dependencies']]
    staged_paths += [ROOT/'research/2026-10-13-astra-legal-row-support-2115z/lean/Astra/ActualLegalRowSupport.lean',
                    ROOT/'research/2026-10-13-astra-legal-row-support-2115z/lean/AstraLegalRowSupport.lean',
                    ROOT/'research/2026-10-13-astra-selected-copy-readout-2250z/lean/Astra/SelectedCopyReadout.lean',
                    ROOT/'research/2026-10-13-astra-selected-copy-readout-2250z/lean/AstraSelectedCopy.lean']
    staged = []
    for p in staged_paths:
        rel = p.parts[p.parts.index('lean')+1:]
        staged.append(dict(pin(p), module='.'.join(Path(*rel).with_suffix('').parts),
                           destination=str(Path(*rel)), imports=imports(p)))
    for r in delta['staged_astra_dependencies']:
        assert pin(ROOT/r['path'])['sha256'] == r['sha256']
    new_owned = [r for r in owned if not r['active_profile_member']]
    common = dict(schema='astra.source-only-follow-on-plan.v1',
        status='STATIC SOURCE PLAN; no official import query, materialization, compile, axiom audit or object-cache authentication',
        baseline_public_commit=selected['accepted_package_commit'],
        inputs=[pin(p) for p in [SEL, DELTA, ACTIVE, EXTERNAL, UPSTREAM, ROOT/selected['graph_path']]],
        active_plan_unchanged=True, mathlib_pin=ext['mathlib_pin'],
        compiler_sha256_recorded_not_rechecked=ext['compiler_sha256'],
        package_dependency_pins=ext['dependencies'],
        method='Recompute source bytes/Git blobs; nested-comment-aware literal import headers against selected graph. No Lean --deps/--src-deps invocation.')
    save('FOLLOW-ON-DEPENDENCIES.json', dict(common, owned_roots=roots,
        owned_count=len(owned), owned_order=order, owned=owned,
        new_owned_count=len(new_owned), new_owned_source_bytes=sum(r['bytes'] for r in new_owned),
        new_owned_mathlib=[r['module'] for r in new_owned if r['module'].startswith('Mathlib.')],
        new_astra_sources=staged, selected_copy_route='Controlled literal all-panel projectivity is inside this469 closure. Actual source-only Astra.SelectedCopyReadout now composes it under one PMF; its source is pinned here, without a compiler or axiom claim.',
        full1613_aggregate='Retained as authenticated source baseline, not the469 narrow target and not claimed freshly rebuilt.'))
    save('FOLLOW-ON-EXTERNAL-ROOTS.json', dict(common,
        direct_roots=sorted(direct_external), root_records=external_records,
        new_direct_mathlib_roots=[r['module'] for r in delta['new_direct_external_roots']],
        new_direct_mathlib_roots_already_in_active_plan=True,
        official_additions_outside_active_plan=[dict(records[r['module']], upstream_auth=r)
                                               for r in upstream['bodies']],
        current_external_count=len(official), future_external_closure_count=None,
        explanation='All98 direct Mathlib roots are source-equal entries in current3591 plan; Omega is a toolchain source. Two additional owned Mathlib modules are not in3591. Existing official transitive edges are retained only as planning evidence. Future official query must confirm closure and output paths before reuse/build.'))
    selected_decls = {
        'G4WholeProfileDetermination':['actual_randomized_common_row_finite_tree_law_determination','actual_finite_randomized_common_menu_responses'],
        'G4ActualSparseCertificateExistence':['actual_exists_sparse_observable_certificate','actual_matching_moments_restrict_bank'],
        'G7OriginalSurvivalCoverage':['every_actual_source_has_fixed_calendar_representative'],
        'G4PairedNaturalTreeCertificate':['actual_legal_paired_certificate_iff_noHybrids','actual_ordinary_target_shared_queries_all_future']}
    inspected = []
    for n, names in selected_decls.items():
        r = records[n]; p = ROOT/r['path']; actual=pin(p)
        assert all(actual[k]==r[k] for k in ['sha256','git_blob','bytes'])
        inspected.append(dict(r, declarations=[signature(p,k) for k in names]))
    consumer = ROOT/'research/2026-10-13-dot-g3-certified-consumer-0631z/G3CertifiedCommonBoundedWitness.lean'
    required = ['actual_finite_equal_arm_reduction','physicalSteps_trace','traceHybrid','traceDecoration',
        'tracePrimitive','traceHybrid_marks','trace_joint_row_law','equalArmReduced_physical_hybrid_bound',
        'projected_protected_mask','markedSteps_count','physicalSteps_marked','protected_original_code_coverage',
        'markedSteps_outer','trace_tree_bucket_law']
    scan = {n:[] for n in required}
    for r in records.values():
        s = uncomments((ROOT/r['path']).read_text())
        for n in required:
            if re.search(r'(?m)^\s*(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure)\s+'+re.escape(n)+r'\b',s):scan[n].append(r['module'])
    save('PHYSICAL-PROVIDER-GAP.json', dict(schema='astra.selected1613-physical-provider-gap.v1',
        selection=pin(SEL), scope='Local selected1613 source bodies and exact existing consumer only; no repeated remote search and no impossibility claim.',
        consumer=dict(pin(consumer),imports=imports(consumer),declaration=signature(consumer,'actual_certificate_bounded_original_coverage')),
        missing_provider=dict(module='G4ProtectedCommonRepresentative',sha256='0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04',recorded_bytes=137239),
        selected1613_contains_missing_module='G4ProtectedCommonRepresentative' in records,
        required_provider_declaration_name_scan=scan, inspected_alternatives=inspected,
        result='No authenticated selected1613 alternative located that constructs the required bounded admitted protected physical representative. Finite tree support/determination, fixed-calendar reparameterization and NoHybrids recognition do not discharge that obligation.',
        missing_mathematical_contract='One physical trace supplies R, retained hybrid injection J and raw-edge decoration D, protected provenance and admission, exact certificate-derived hybrid bound and fixed external ProtectedCode membership, before every future permitted joint control law and copy allocation; no unknown target field in certificate.',
        execution='No proof substitution, axiom, compiler, control or source-existence assumption introduced.'))
    extension=ROOT/'research/2026-10-13-astra-unified-accepted-extension-2340z'
    catalog=read(extension/'SOURCE-CATALOG.json')
    for r in staged:
        matches=[x for x in catalog['sources'] if x['module']==r['module']]
        assert matches and all(x['sha256']==r['sha256'] for x in matches),r['module']
    materializer=extension/'materialize_extension.py'
    save('MATERIALIZATION-CONFIG.json',dict(common,
        destination_policy='New isolated destination selected by build owner; never replace active workspace or mutate prior319/3591 plan.',
        selected_source_materializer=pin(materializer),
        materialization_source_command_not_run_here=['python3','-B',str(materializer.relative_to(ROOT)),'--out','NEW_EMPTY_DESTINATION'],
        existing_owner_package_evidence=[pin(extension/name) for name in ['SOURCE-CATALOG.json','EXECUTION-HANDOFF.json',
            'evidence/MATERIALIZED-SOURCE-SELECTION.json','evidence/MATERIALIZED-lakefile.lean',
            'evidence/materialization-v2/RECEIPT.json']],
        inherited_full_source_scope='Preserve all1613 selected modules and accepted aggregate byte identities; own Mathlib paths remain exactly selected.',
        exact_increment_sources_already_in_owner_catalog=staged,
        intended_narrow_lake_targets=['AstraSelectedCopy','AstraLegalRowSupport'],
        target_commands_not_executed=[['lake','build','AstraSelectedCopy'],['lake','build','AstraLegalRowSupport']],
        full_unified_aggregate_policy='Do not relabel the narrow469 target a fresh full1613 rebuild. Full accepted aggregate remains a separate preserved entry.',
        required_before_execution=['Authenticate destination source bytes and ensure no namespace collision or provider drift.',
            'Run official compiler import query under existing owner/resource policy; produce new additive external plan.',
            'Authenticate compatible external objects against exact source/compiler/import state; no reuse inferred from presence.',
            'Compile pending adapter/legal-row sources serially with actual closed receipts and transitive axiom output.',
            'Keep selected-copy native correspondence and physical bounded representative obligations separate.'],
        materialization_performed_by_this_lane=False,
        owner_materialization='Root reports isolated source materialization/byte authentication PASS; exact source/configuration and receipt pins linked here, without rerunning it or inferring object execution.',
        compiler_query_performed=False, lake_target_executed=False))
    for name in ['FOLLOW-ON-DEPENDENCIES.json','FOLLOW-ON-EXTERNAL-ROOTS.json','PHYSICAL-PROVIDER-GAP.json','MATERIALIZATION-CONFIG.json']:
        print(json.dumps(pin(HERE/name)))


if __name__ == '__main__':
    main()
