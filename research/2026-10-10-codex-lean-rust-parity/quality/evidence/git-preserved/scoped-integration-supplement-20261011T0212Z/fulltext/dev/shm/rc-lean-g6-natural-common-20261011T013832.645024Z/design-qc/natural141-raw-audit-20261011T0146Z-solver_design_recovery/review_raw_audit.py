"""Independent saved raw-audit exact comparison; no producer or target import."""
from datetime import datetime, timezone
import gzip
import hashlib
import json
from pathlib import Path
import re

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
W = Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
Q = W / 'design-qc/natural141-raw-audit-20261011T0146Z-solver_design_recovery'
FOUNDATIONS = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def pin(p, h):
    assert sha(p) == h, str(p)
    return {'path': str(p), 'sha256': h, 'bytes': p.stat().st_size}

parentp = P / 'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json'
parentpin = pin(parentp, '1f45babae7a183dc1638ebfd7de210fddcf2dd872e8498f3f80ede4d06e9fcc2')
parent = json.loads(parentp.read_bytes())
pt = parent['targets']['current/connected']
pargz = P / 'lean' / parent['evidence'] / pt['audit_distribution']
parraw = gzip.decompress(pargz.read_bytes())
assert hashlib.sha256(parraw).hexdigest() == pt['audit_raw_sha256'] == '554a83beeeef1ebc438451d051bead1030796a36bac0db3c8f6e803c5ec09813'
old = {x['name']: x for x in json.loads(parraw)['declarations']}
assert len(old) == 100985
del parraw
rawp = W / '.build/runs/20261011T014055.249073Z/attempts/00003-OwnedAudit/work/AUDIT-RESULT.json'
rawpin = pin(rawp, '6df3d6c8f923bd4d0ee05af2bab474bbed334bf2184879aa5b0354458d217021')
audit = json.loads(rawp.read_bytes())
new = {x['name']: x for x in audit['declarations']}
assert len(new) == audit['declaration_count'] == 3486
assert sum(x['kind'] == 'theorem' for x in new.values()) == audit['theorem_declaration_count'] == 2293
assert len(audit['selected_modules']) == 141
assert not audit['owned_axioms'] and not audit['nonstandard_axiom_rows'] and not audit['missing_modules']
assert all(set(x['axioms']) <= FOUNDATIONS for x in new.values())
assert len(new.keys() & old.keys()) == 3417 and len(new.keys() - old.keys()) == 69
owner_pairs = {
    'UnifiedLean.Source.UniformizedSourceStep.globalRateBound.eq_1': ['RationalNaturalCellWitness', 'G7SourceStepRelabelling'],
    'Nanuq.Source.EdgeGraph.IsHybrid.eq_1': ['G1SpliceDegrees', 'G7OriginalRelabelling'],
    'UnifiedLean.Source.NativeIndependentPairMixture.HybridProbabilities.mk.congr_simp': ['UnifiedLean.Source.NativeFairCurrentPosition', 'G7OriginalRelabelling'],
    'UnifiedLean.Source.SourceInitializedCalendar.finalDate.eq_1': ['G5OriginalEpochChart', 'G6OriginalCommonPrefix'],
    'UnifiedLean.Source.SourceNaturalInitialization.originalRegister.eq_1': ['PrivateSeedFactorization', 'G7NaturalWordRelabelling'],
    'GProgram.G5.Calendar.mk.congr_simp': ['G1SharpCoreCombDefinition', 'G7OriginalRelabelling'],
    'UnifiedLean.Source.UniformizedSourceStep.choiceRate.eq_1': ['ActualPopulationRate', 'G7SourceStepRelabelling'],
    'Nanuq.Source.EdgeGraph.outDegree.eq_1': ['GraphSwitchingDegree', 'G7OriginalCensus'],
    'Nanuq.Source.EdgeGraph.outDegree.congr_simp': ['G1SpliceDegrees', 'G7OriginalCensus'],
    'MeasureTheory.Measure.toPMF.congr_simp': ['NaturalCalendarPastAdmission', 'G7CoinReindexing'],
    'UnifiedLean.Source.SourceCalendarCompatibility.originalDates.eq_1': ['OriginalCalendarPattern', 'G7CalendarAgendaRelabelling'],
    'UnifiedLean.Source.SourceInitializedCalendar.finalDate.eq_2': ['G5OriginalEpochChart', 'G6OriginalCommonPrefix']
}
aliasrow = 'UnifiedLean.Source.SourceInitializedCalendar.finalDate.eq_def'
oldalias = '_private.G5OriginalEpochChart.0.UnifiedLean.Source.SourceInitializedCalendar.finalDate.match_1.splitter'
newalias = '_private.G6OriginalCommonPrefix.0.UnifiedLean.Source.SourceInitializedCalendar.finalDate.match_1.splitter'
differences = []
for n in sorted(new.keys() & old.keys()):
    assert set(new[n]) == set(old[n])
    change = {k: [old[n][k], new[n][k]] for k in old[n] if old[n][k] != new[n][k]}
    if change:
        if n in owner_pairs:
            assert change == {'module': owner_pairs[n]}, n
        else:
            assert n == aliasrow and set(change) == {'module', 'body_references'}
            assert change['module'] == ['G5OriginalEpochChart', 'G6OriginalCommonPrefix']
            a, b = change['body_references']
            assert len(a) == len(b) and [i for i in range(len(a)) if a[i] != b[i]] == [15]
            assert a[15] == oldalias and b[15] == newalias
        differences.append({'name': n, 'differences': change})
    assert new[n]['kind'] == old[n]['kind'] and new[n]['type_references'] == old[n]['type_references'] and new[n]['axioms'] == old[n]['axioms']
assert len(differences) == 13 and {r['name'] for r in differences} == set(owner_pairs) | {aliasrow}
alias_pairs = []
for end in ('splitter', 'eq_1', 'eq_2'):
    a = '_private.G5OriginalEpochChart.0.UnifiedLean.Source.SourceInitializedCalendar.finalDate.match_1.' + end
    b = '_private.G6OriginalCommonPrefix.0.UnifiedLean.Source.SourceInitializedCalendar.finalDate.match_1.' + end
    assert {k: v for k, v in old[a].items() if k not in ('name', 'module')} == {k: v for k, v in new[b].items() if k not in ('name', 'module')}
    alias_pairs.append({'accepted_parent': old[a], 'actual_context': new[b], 'all_fields_equal_except_name_and_module': True})
calendarrow = 'UnifiedLean.Source.SourceCalendarCompiler.calendarTail.eq_def'
assert new[calendarrow] == old[calendarrow]

acp = P / 'lean/G6-ORIGINAL-PARALLEL-ARM-TRANSPORT-117-ACCEPTANCE.json'
acpin = pin(acp, '3a97ebdad3974a0873e5a1d9f68757f3ecc87bdee1b2b3669be0c6a6eba3a48e')
ac = json.loads(acp.read_bytes())
pcp = P / ac['certificate']['path']
pcpin = pin(pcp, ac['certificate']['sha256'])
pc = json.loads(pcp.read_bytes())
pt = pc['targets']['extraction/g6-original-parallel-arm-transport-f40a0d66']
pgz = P / 'lean' / pc['evidence'] / pt['audit_distribution']
praw = gzip.decompress(pgz.read_bytes())
assert hashlib.sha256(praw).hexdigest() == pt['audit_raw_sha256'] == 'd76d61da1557b3f607ec9965744d801dea16a85f833837001e5d12e67a668b43'
pa = {x['name']: x for x in json.loads(praw)['declarations']}
parallel = {n: x for n, x in new.items() if x['module'] == 'G6OriginalParallelArmTransport'}
assert len(parallel) == 24 and all(pa[n] == x for n, x in parallel.items())
assert set(parallel) <= new.keys() - old.keys()

freezep = Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z/metadata/factor-ite-true-proof-repair-3fc98f89-20261011T012921.157357Z/PROPOSAL-FREEZE-V10-ITE-TRUE.json')
freezepin = pin(freezep, 'd54d69c760f24b6e6a2e6fb7310c6b6d5a489250663bfafb82b0adda62d9da9f')
freeze = json.loads(freezep.read_bytes())
authored = {}
for s in freeze['sources']:
    ns = 'GProgram.G6.' + ('OriginalCommonPrefix' if s['module'] == 'G6OriginalCommonPrefix' else 'NaturalCommonForestFactorization') + '.'
    for h in s['declarations']:
        n = ns + h['name']
        if h['header'].startswith('private '):
            n = '_private.' + s['module'] + '.0.' + n
        assert n in new and new[n]['module'] == s['module']
        assert new[n]['kind'] == ('theorem' if re.match(r'(?:private )?theorem\b', h['header']) else 'definition')
        authored[n] = new[n]
assert len(authored) == 29
freshunique = {n: x for n, x in new.items() if n not in old and n not in parallel}
assert len(freshunique) == 45 and set(authored) <= set(freshunique)
assert {x['module'] for x in freshunique.values()} == {'G6OriginalCommonPrefix', 'G6NaturalCommonForestFactorization'}
prefixunique = [x for x in freshunique.values() if x['module'] == 'G6OriginalCommonPrefix']
factorunique = [x for x in freshunique.values() if x['module'] == 'G6NaturalCommonForestFactorization']
assert len(prefixunique) == 14 and sum(x['kind'] == 'theorem' for x in prefixunique) == 10
assert len(factorunique) == 31 and sum(x['kind'] == 'theorem' for x in factorunique) == 22
owned = [x for x in new.values() if x['module'] in {'G6OriginalCommonPrefix', 'G6NaturalCommonForestFactorization'}]
assert len(owned) == 48 and sum(x['kind'] == 'theorem' for x in owned) == 35
generatedunique = {n: x for n, x in freshunique.items() if n not in authored}
assert len(generatedunique) == 16 and sum(x['kind'] == 'theorem' for x in generatedunique.values()) == 12
report = {
    'schema': 'natural141_actual_raw_audit_precise_context_design_qc_v1',
    'contributor': 'Codex / solver_design_recovery',
    'observed_utc': datetime.now(timezone.utc).isoformat(),
    'reviewer_sha256': sha(Path(__file__)),
    'status': 'PASS_SAVED_RAW_141_AUDIT_EXACT_13_CONTEXT_RECORD_QUALIFICATION',
    'actual_raw_audit': rawpin, 'accepted1504_certificate': parentpin, 'accepted1504_raw_audit_sha256': '554a83beeeef1ebc438451d051bead1030796a36bac0db3c8f6e803c5ec09813', 'accepted_parallel117': acpin, 'accepted_parallel117_certificate': pcpin, 'frozen_actual_new_sources': freezepin,
    'counts': {'selected_modules': 141, 'declarations': 3486, 'theorems': 2293, 'inherited1504_names': 3417, 'literal_inherited1504_records': 3404, 'qualified_exact_context_differences': 13, 'owner_only_differences': 12, 'owner_and_exact_alias_differences': 1, 'already_accepted_parallel_names_absent1504': 24, 'unique_new_source_names': 45, 'unique_new_theorems': 32, 'unique_new_definitions': 13, 'prefix_unique_new': 14, 'factor_unique_new': 31, 'new_source_owner_labeled_records': 48, 'existing_finalDate_heads_owner_labeled_to_prefix': 3, 'authored_headers': 29, 'unique_generated_names': 16, 'unique_generated_theorems': 12, 'unique_generated_definitions': 4},
    'exact_inherited_differences': differences,
    'finalDate_alias_record_pairs': alias_pairs,
    'SourceCalendar_calendarTail_eq_def_literal_parent_match': True,
    'already_accepted_parallel24_records_literal_match': list(parallel.values()),
    'authored_new_records': list(authored.values()),
    'unique_generated_new_records': list(generatedunique.values()),
    'all_kind_type_reference_axiom_fields_inherited_equal': True,
    'qualification': ['This independently qualifies only the exact13 observed record differences. No generic owner/body/type/proof normalization and no full1504 metadata retention/coherent union claim.', 'Prefix17-owner and factor31-owner counts are not48 unique new declarations. Three inherited finalDate heads are owner-labeled to prefix. Exactly45 unique new names (14prefix+31factor), including16 generated, are observed relative accepted1504 plus separate acceptedf40.', 'Three new finalDate private aliases equal their exact accepted G5OriginalEpochChart counterpart records in every field except name/module; the eq_def proof body changes exactly one referenced private splitter.', 'Raw saved audit/source names and standard foundation metadata only. Full compiler/native/transport/capture/preservation QA and root formal scoped acceptance remain separate. No producer/helper/target import or invocation.'],
    'target_imports_or_producers_invoked': 0,
    'overlay_writes': 0
}
out = Q / 'NATURAL141-RAW-AUDIT-EXACT-CONTEXT-QC-ATTEMPT1.json'
with out.open('x') as f:
    json.dump(report, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps({'receipt': str(out), 'sha256': sha(out), 'status': report['status'], 'counts': report['counts']}))
