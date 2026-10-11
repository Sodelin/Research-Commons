"""Read-only frozen provider-block/source and scope review, no target import."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

P = Path('/workspace/Research-Commons/research/2026-10-10-codex-lean-rust-parity')
W = Path('/dev/shm/rc-lean-g6-natural-common-20261011T013832.645024Z')
OW = Path('/dev/shm/rc-lean-g6-natural-common-20261011T011433.283909Z')
Q = W / 'design-qc/natural141-scope-challenge-20261011T0149Z-solver_design_recovery'
M1 = OW / 'metadata/legal-positive-twoport-bin-provider-map-20261011T013349.662735Z/PROVIDER-MAP.json'
M2 = OW / 'metadata/legal-positive-twoport-bin-constructor-map-v2-20261011T014645.303868Z/CONSTRUCTOR-PROVIDER-MAP-V2.json'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert sha(M1) == 'b9f17f6af9cc508dbf8e1fcacf740cf9cb04d58088bb452bd777b8abc0cea767'
assert sha(M2) == 'a8ae28ac04e54e9fa8fb11ad9747b1d8ed667899a498b3b25aed28e4f44ef7e1'
a, b = json.loads(M1.read_bytes()), json.loads(M2.read_bytes())
parent = json.loads((P / 'lean/HISTORY-SURVIVAL-UNION-1504-CERTIFICATE.json').read_bytes())
forestfreeze = json.loads((P / 'lean/proposals/reuse-integration-20261010T2138Z/forest-register-compression/PROPOSAL-FREEZE.json').read_bytes())
naturalfreeze = json.loads((OW / 'metadata/factor-ite-true-proof-repair-3fc98f89-20261011T012921.157357Z/PROPOSAL-FREEZE-V10-ITE-TRUE.json').read_bytes())
special_imports = {'G6OriginalForestRegisterCompression': forestfreeze['source']['imports'], 'G6NaturalCommonForestFactorization': naturalfreeze['sources'][1]['imports']}
rows, blocks = [], 0
for r in a['providers']:
    p = Path(r['path'])
    assert sha(p) == r['sha256'] and p.stat().st_size == r['bytes']
    text = p.read_text()
    if 'literal_imports' in r:
        expected = r['literal_imports']
    else:
        assert r['module'] in special_imports
        expected = special_imports[r['module']]
    assert re.findall(r'^import\s+(\S+)', text, re.M) == expected
    for d in r['declarations']:
        # V1 is exclusive-end-line and whitespace-trimmed block, not inclusive.
        block = ''.join(text.splitlines(True)[d['line_start'] - 1:d['line_end'] - 1]).strip()
        assert hashlib.sha256(block.encode()).hexdigest() == d['declaration_block_sha256'], (r['module'], d['name'])
        assert hashlib.sha256(d['header'].encode()).hexdigest() == d['header_sha256'] and d['header'] in text
        blocks += 1
    if r['acceptance'].startswith('EXACT_SOURCE_INCLUDED_ACCEPTED1504'):
        assert parent['source_pins'][r['module']] == r['sha256']
    rows.append({'module': r['module'], 'path': str(p), 'sha256': r['sha256'], 'bytes': r['bytes'], 'declaration_blocks': len(r['declarations']), 'acceptance': r['acceptance']})
for r in b['additional_providers']:
    p = Path(r['path'])
    assert sha(p) == r['sha256'] == r['accepted1504_sha256'] == parent['source_pins'][r['module']]
    assert p.stat().st_size == r['bytes']
    text = p.read_text()
    assert re.findall(r'^import\s+(\S+)', text, re.M) == r['imports']
    for d in r['declarations']:
        block = ''.join(text.splitlines(True)[d['lines'][0] - 1:d['lines'][1]])
        assert block == d['literal_block'] and hashlib.sha256(block.encode()).hexdigest() == d['block_sha256']
        assert d['literal_header'] in text
        blocks += 1
    rows.append({'module': r['module'], 'path': str(p), 'sha256': r['sha256'], 'bytes': r['bytes'], 'declaration_blocks': len(r['declarations']), 'acceptance': 'accepted1504 exact source/import'})
chart = Path('/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/source-store/20df02223f9c2c214056f50d4bfa43f7e68ee35a93aead431ef2a02bd81f1163.lean')
assert sha(chart) == parent['source_pins']['G6OriginalWholeEdgeChartConsumer'] == '20df02223f9c2c214056f50d4bfa43f7e68ee35a93aead431ef2a02bd81f1163'
failure = Q / 'OWN-INLINE-PROVIDER-SCHEMA-PREFLIGHT-FAILURE.json'
with failure.open('x') as f:
    json.dump({'status': 'PRESERVED_OWN_READER_SCHEMA_ASSUMPTION_FAILURE', 'contributor': 'Codex / solver_design_recovery', 'error_type': 'KeyError', 'field': 'literal_imports', 'explanation': 'Own inline preliminary reader assumed all V1 provider rows carried literal_imports. Two separately scoped consumer rows omit that field. Corrected reader allows only those two exact module names and compares source imports to their independently pinned original freezes. No target/source/map mutation or PASS output occurred.'}, f, indent=2, sort_keys=True)
    f.write('\n')
findings = [
    {'interface': 'Existing rate/coin bank', 'provider': '593 ratesFromLengths/ratesFromSurvival;20df whole_edge_original_coin_chart', 'conclusion': 'One bank already realizes each supplied positive original-edge exposure/open survival and interior original gamma on a supplied strict Calendar before every original mask.', 'remaining': 'Graph/calendar/class admission and actual local/bin/timed operation binding; no new logarithmic bank or rational-log effectivity is inferred.'},
    {'interface': 'Natural COMMON law', 'provider': 'current3fc original initialized history + NoPrivateWordRead', 'conclusion': 'Original private seed is naturally drawn once; retained selector support and its original gamma=P(parent1) are marginalized with arbitrary Old on the entire erased entering Code and every endpoint vector. Full register/forest and all-live-at-h premise retained.', 'remaining': 'No fixed complete-Code Bernoulli mixture. Proper outside panels need actual copy restriction/opaque graft/separation. Long-arm orientation gives gamma or1-gamma; delta0 is an identity residual after a positive baseline.'},
    {'interface': 'Physical word and single exit', 'provider': '805698 actual_word_exit_population / actual_cap_m_finite_two_port_g1', 'conclusion': 'A supplied original endpoint-typed TwoPortWord already derives sole physical exit and full carried subtree/register/correlated history law. Literal prefix tied-date/node split is separately supplied by a080.', 'remaining': 'Bind actual generated-calendar interior to that actual physical word and actual local support. A prefix split does not assert whole interior equality or authorize changing unrelated active populations.'},
    {'interface': 'Old tags and future', 'provider': '2e7 actual_constant_bin_forest_law / actual_word_exit_reconstructed;6c002 actual_guarded_unranked_bin_future', 'conclusion': 'Full tagged forest decoder, original exit reconstruction and upper no-read continuation already exist.', 'remaining': 'Instantiate CutRefines, wordBinContract, strict upper guard/date split, full erased unranked view and original outside register/population embedding. An arbitrary future may read the private seed; these maps do not invert calibrated observations.'},
    {'interface': 'Scalar word and observation', 'provider': 'actual_no_loss_append; separate forest101 centered-generator fibre law', 'conclusion': 'The scalar product requires its reachable row-constant hq. The full-forest/Old law and finite generator fibre certificate have their distinct explicit domains.', 'remaining': 'No arbitrary whole-word scalar product, timed observation, calibrated decoder, native literal-Code/refinement or source provenance is inferred. New G4 hand/draft claims retain their separate kernel gates.'},
    {'interface': 'Meaningful finite constructor contract', 'provider': 'read-only V2 concrete inverse nonroot bridge insertion', 'conclusion': 'Concrete V+2/E+3 carrier, four ordered occurrences, retained old ages with new one-third/two-thirds dates, connector/bigon/connector word, original registry extension and deletion Step with explicit carrier equivalences back to S.', 'remaining': 'These outputs are still unproved: RootedBinary/DAG/LSA/CutChild/calendar/blob admission, physical word and inverse Step field equality. The old outer-labelled planar/galled master class needs an explicit extra witness. Do not substitute desired kernel equality as input.'},
    {'interface': 'Positive bounded biological source', 'provider': 'Oct1 AppendixA.2; accepted forest101', 'conclusion': 'Old hand algebra gives a=1-(1-X)/(4K+1), X_res=X/a^(2K), positive armsa/az plus connectora;K0 ordinary positive edge. Forest101 transfers one supplied centered-generator certificate over full register/forest fibres.', 'remaining': 'Formal admitted insertion/shared-bank/cohort/refinement and stochastic Poissonization/Euler/error budgets remain downstream. Signed generator equality is not arbitrary PMF-mixture realizability or a formal polynomial-length biological approximation theorem.'}
]
report = {'schema': 'natural141_existing_legal_source_calibrated_decoder_scope_challenge_v1', 'contributor': 'Codex / solver_design_recovery', 'observed_utc': datetime.now(timezone.utc).isoformat(), 'reviewer_sha256': sha(Path(__file__)), 'status': 'PASS_READ_ONLY_SCOPE_AND_PROSPECTIVE_CONSTRUCTOR_CONTRACT_REVIEW; not a proved constructor', 'provider_maps': [{'path': str(M1), 'sha256': sha(M1)}, {'path': str(M2), 'sha256': sha(M2)}], 'authenticated_source_records': rows, 'authenticated_declaration_blocks': blocks, 'whole_edge_original_coin_chart': {'path': str(chart), 'sha256': sha(chart)}, 'actual_natural_source': '3fc98f898f705bf778fa5b2d448ae5e05ce00d262bc3048042f08c07921edac4', 'findings': findings, 'own_schema_correction': {'path': str(failure), 'sha256': sha(failure)}, 'qualification': 'Bounded existing-body readback and scope challenge, not universal absence of providers, new mathematical acceptance, a proved outline, fullG6/G7/G4/native/master closure or promotion of the fixed65-ID register. Full3fc transport/capture/byte QA is a separate acceptance gate.', 'new_theorem_sources_or_decoders_authored': 0, 'target_imports_compiler_native_helper_invocations': 0, 'git_or_external_mutations': 0, 'overlay_writes': 0}
out = Q / 'EXISTING-LEGAL-SOURCE-AND-CALIBRATED-DECODER-SCOPE-CHALLENGE-ATTEMPT2.json'
with out.open('x') as f:
    json.dump(report, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps({'receipt': str(out), 'sha256': sha(out), 'source_records': len(rows), 'declaration_blocks': blocks}))
