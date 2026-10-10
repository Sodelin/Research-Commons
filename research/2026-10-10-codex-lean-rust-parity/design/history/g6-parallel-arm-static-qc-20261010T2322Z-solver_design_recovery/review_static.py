#!/usr/bin/env python3
"""Independent source/byte QC only; never import or execute target providers."""
import hashlib
import json
import pathlib
import re
from datetime import datetime, timezone

REPO = pathlib.Path('/workspace/Research-Commons')
PACKET = REPO / 'research/2026-10-10-codex-lean-rust-parity'
OWN = pathlib.Path(__file__).resolve().parent
PROPOSAL = PACKET / 'lean/proposals/reuse-integration-20261010T2138Z/parallel-arm-transport'
SOURCE_SHA = 'f40a0d66db43984f05ca250dc1d4e9e79372141a498732414d8acde11162d6dc'
FREEZE_SHA = '73e28655aa7277e838c37bf84e56bfe275e5fc592ddc137baa6ce66c99cdb24b'

def pin(path, expected=None):
    path = pathlib.Path(path)
    raw = path.read_bytes()
    digest = hashlib.sha256(raw).hexdigest()
    if expected is not None:
        assert digest == expected, (str(path), digest, expected)
    return {'path': str(path), 'sha256': digest, 'bytes': len(raw)}

def strip_comments(text):
    """Remove nested Lean comments, retaining newlines for source positions."""
    out, depth, index = [], 0, 0
    while index < len(text):
        pair = text[index:index + 2]
        if pair == '/-':
            depth += 1
            out.extend('  ')
            index += 2
        elif depth and pair == '-/':
            depth -= 1
            out.extend('  ')
            index += 2
        elif not depth and pair == '--':
            end = text.find('\n', index)
            if end < 0:
                end = len(text)
            out.extend(' ' * (end - index))
            index = end
        else:
            out.append(text[index] if not depth or text[index] == '\n' else ' ')
            index += 1
    assert depth == 0, 'unterminated comment'
    return ''.join(out)

def imports(text):
    result = []
    for line in strip_comments(text).splitlines():
        match = re.match(r'^\s*(?:public\s+)?import\s+(.+?)\s*$', line)
        if match:
            result.extend(match.group(1).split())
    return result

freeze_pin = pin(PROPOSAL / 'PROPOSAL-FREEZE.json', FREEZE_SHA)
freeze = json.loads((PROPOSAL / 'PROPOSAL-FREEZE.json').read_text())
source_path = REPO / freeze['source']['path']
source_pin = pin(source_path, SOURCE_SHA)
version_pin = pin(REPO / freeze['source']['immutable_version'], SOURCE_SHA)
source = source_path.read_text()
assert imports(source) == freeze['source']['imports']
context = freeze['accepted_provider_context']
certificate_pin = pin(REPO / context['certificate'], context['certificate_sha256'])
certificate = json.loads((REPO / context['certificate']).read_text())
parent_qc_pin = pin(REPO / context['root_qc'], context['root_qc_sha256'])
providers = {entry['module']: entry for entry in context['providers']}
assert len(providers) == len(context['providers']) == 116
provider_pins, external = [], set()
for module, entry in providers.items():
    item = pin(REPO / entry['accepted_source'], entry['sha256'])
    assert certificate['source_pins'][module] == item['sha256'], module
    actual_imports = imports(pathlib.Path(item['path']).read_text())
    assert actual_imports == entry['imports'], (module, actual_imports, entry['imports'])
    for imported in actual_imports:
        if imported not in providers:
            assert imported.startswith(('Mathlib.', 'Lean.')), (module, imported)
            external.add(imported)
    item.update(module=module, imports=actual_imports)
    provider_pins.append(item)

root = freeze['source']['module']
assert root not in providers and root not in certificate['source_pins']
graph = {module: [m for m in entry['imports'] if m in providers]
         for module, entry in providers.items()}
graph[root] = imports(source)
reached, active = set(), set()
def visit(module):
    assert module not in active, ('import cycle', module)
    if module in reached:
        return
    active.add(module)
    for parent in graph[module]:
        visit(parent)
    active.remove(module)
    reached.add(module)
visit(root)
assert reached == set(providers) | {root}
assert len(reached) == freeze['intended_target']['exact_import_closure_size'] == 117
assert freeze['intended_target']['parents'] == 116

code = strip_comments(source)
assert not re.search(r'\b(?:sorry|admit|axiom|unsafe|partial)\b', code)
starts = list(re.finditer(r'^(?:private )?(?:noncomputable )?(?:def|theorem)\s+(\w+)', code, re.M))
expected_names = [
    'edgeSwap', 'arm_swap_source', 'arm_swap_target', 'edgeGraph_eq',
    'rootedBinary_eq', 'arm_network_eq', 'arm_parent_occurrence',
    'arm_rate_occurrence', 'castCode', 'castCode_val', 'castCode_time',
    'armCode', 'armCode_val', 'armCode_full_forest_register',
    'armCode_constant_pulse', 'armCode_time_kernel',
    'actual_parallel_arm_full_forest_transport',
]
assert [match.group(1) for match in starts] == expected_names
lines = source.splitlines(keepends=True)
declarations = []
for expected, name in zip(freeze['source']['declarations'], expected_names):
    header = ''.join(lines[expected['line'] - 1:]).split(':=', 1)[0].strip()
    assert header == expected['header'], (name, header)
    assert hashlib.sha256(header.encode()).hexdigest() == expected['sha256']
    declarations.append(dict(expected, name=name,
                             visibility='private' if header.startswith('private ') else 'public',
                             kind='theorem' if 'theorem ' in header else 'definition'))
assert len(declarations) == 17
assert sum(d['visibility'] == 'public' for d in declarations) == 12
assert sum(d['visibility'] == 'private' for d in declarations) == 5
assert sum(d['kind'] == 'theorem' for d in declarations) == 14

receipt = {
    'schema': 'independent_lean_static_contract_qc_v1',
    'contributor': 'Codex / solver_design_recovery',
    'observed_utc': datetime.now(timezone.utc).isoformat(),
    'status': 'PASS_STATIC_SOURCE_AND_SCOPE_QC; new proposal remains uncompiled',
    'reviewer': pin(__file__),
    'source': source_pin, 'immutable_source_version': version_pin,
    'proposal_freeze': freeze_pin,
    'accepted_1504_certificate': certificate_pin, 'accepted_1504_root_qc': parent_qc_pin,
    'exact_original_imports': imports(source),
    'independent_import_closure': {
        'executed_proposal_closure_size': 117, 'accepted_parents': 116,
        'new_source_modules': 1, 'all_sources_and_literal_imports_matched': True,
        'protected_mathlib_guard_staging_is_separate': True,
        'external_library_imports': sorted(external),
    },
    'authored_declarations': declarations,
    'authored_counts': {'all': 17, 'public': 12, 'private_helpers': 5,
                        'public_theorems': 10, 'public_definitions': 2,
                        'private_theorems': 4, 'private_definitions': 1},
    'provider_source_pins': provider_pins,
    'static_contract_findings': [
        {'heads': ['edgeSwap', 'arm_swap_source', 'arm_swap_target', 'edgeGraph_eq',
                   'rootedBinary_eq', 'arm_network_eq'],
         'finding': 'Actual NonrootBigon supplies two distinct original parent E occurrences with common source and target. Swapping these IDs and fixing V/Copy preserves the actual graph, root and named leaves; only proof fields are discarded by structure equality.'},
        {'heads': ['arm_parent_occurrence', 'arm_rate_occurrence'],
         'finding': 'Transported Boolean b retains its inherited label and names original occurrence !b. Pullback rate bank exchanges those two E entries, preserves all other E rates and the ancestral rate; this is not a forced-bit or gamma complement.'},
        {'heads': ['castCode', 'castCode_val', 'castCode_time', 'armCode', 'armCode_val'],
         'finding': 'Actual accepted snapshot/code transport is returned by equality cast to the equal original source. No arbitrary law, graph admission assumption or target-readout identity is supplied as a field.'},
        {'heads': ['armCode_full_forest_register'],
         'finding': 'V is fixed; every original register value and the entire live carried genealogy are retained. rootForest is the accepted finite rooted labelled unranked live-tree observation, retaining forest structure beyond counts.'},
        {'heads': ['armCode_constant_pulse'],
         'finding': 'All live owners must be at the addressed original hybrid. Actual pulse sends each current owner, including a carried subtree, to parent b and re-encodes genealogy/population; dead population and genealogy fields are canonicalized. Thus the original admitted entering Code needs no extra encoded-input premise.'},
        {'heads': ['armCode_time_kernel', 'actual_parallel_arm_full_forest_transport'],
         'finding': 'Uses the accepted actual sourceTimeKernel relabelling, followed by PMF maps. For arbitrary entering admitted s, all-live-at-hybrid, positive pair-rate bank r and nonnegative t, the full (original register, rooted unranked forest) epoch law after pulse b equals that after pulse !b and edge-swapped rates.'},
    ],
    'remaining_g6_obligations': [
        'A fixed entering Code already has a stored private bit. No Bernoulli mixture is inferred from this conditional identity.',
        'Natural COMMON factorization must bind the original naturally drawn private seed, actual NoPrivateWordRead prefix, and accepted private-seed marginalization/posterior-erasure providers.',
        'Any later register erasure requires an actual no-read continuation; full original-register observations can otherwise distinguish modes.',
        'Use actual source time_add/zero and same-place positive exposure transport to split the smaller arm exposure and nonnegative residual, with original P(true)=parent1 orientation.',
        'Global positive legal source reconstruction, joint full-forest normalization, protected-bin factor production and remaining short-chain obligations are not closed here.',
    ],
    'excluded_claims': [
        'new Lean kernel verification before the sole scheduler runs',
        'natural COMMON mixture for a fixed entering Code',
        'completed bigon exit/calendar/timed-history theorem from the epoch theorem alone',
        'G6 master closure or widened accepted1504 union',
        'native representation refinement, source admission/reconstruction, fitted-source provenance, or universal solver verification',
    ],
    'placeholder_or_new_axiom_tokens': [],
    'target_execution': {'producers': 0, 'compilers': 0, 'helpers': 0, 'native': 0,
                         'adapters': 0, 'reference': 0, 'fitter': 0},
    'source_mutations': [],
    'basis': 'Independently checked source bytes, declaration headers and imports plus manually inspected proof contracts. This receipt is static QC, not Lean elaboration or kernel checking.',
}
destination = OWN / 'G6-PARALLEL-ARM-STATIC-QC-ATTEMPT1.json'
with destination.open('x') as handle:
    json.dump(receipt, handle, indent=2, ensure_ascii=False)
    handle.write('\n')
print(json.dumps(pin(destination)))
