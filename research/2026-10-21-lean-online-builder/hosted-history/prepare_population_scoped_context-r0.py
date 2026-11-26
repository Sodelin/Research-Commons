#!/usr/bin/env python3
"""Select exact retained source commands for the SAME physical population row.

Reuses the existing unique-boundary projection pattern and original compiler
reference audit. This is a source preparer, not a Lean parser, proof checker,
population engine or implementation of an abstract replacement source.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
PUBLIC = ROOT / 'public-packet' if (ROOT / 'public-packet').is_dir() else ROOT


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def checked(path, digest):
    raw = path.read_bytes()
    if sha(raw) != digest:
        raise ValueError('EXACT_RETAINED_SOURCE_REQUIRED: ' + path.name)
    return raw


# Every boundary is an actual original source string, checked for uniqueness.
# None means retain that complete module body. Partial modules preserve their
# original namespace/variable prelude, selected command groups and final end.
SPECS = {
    'SourceNetwork': None,
    'SourceLabelledForest': {
        'namespace': 'GProgram.SourceForest', 'prelude_end': 'inductive Genealogy ',
        'ranges': [
            ('inductive Genealogy ', '/-- Initial state from the original source'),
            ('/-- Recorded output population of an ORIGINAL sample label.', 'theorem merge_coalesces_exact_fibers '),
            ('theorem merge_population_preserved ', 'theorem original_copy_cap '),
            ('variable [DecidableEq E]\n', '/-- Only tokens at the original edge'),
            ('/-- A source population can contain only genealogies', 'theorem initial_source_valid '),
            ('theorem merge_source_valid ', 'theorem exitEdge_source_valid '),
        ],
    },
    'SourceForestKingmanPopulationProjection': {
        'namespace': 'GProgram.SourceForestKingmanPopulationProjection',
        'prelude_end': 'def populationRoots ',
        'ranges': [('def populationRoots ', 'theorem visible_population_pair_is_source_legal')],
    },
    'UnifiedLean.Source.FiniteGenealogyEncoding': None,
    'UnifiedLean.Source.FiniteSourceSnapshot': {
        'namespace': 'UnifiedLean.Source.FiniteSourceSnapshot',
        'prelude_end': '/-- Separate constructor tags',
        'ranges': [
            ('/-- Separate constructor tags', '/-- Snapshot encoding keeps the whole selected genealogy'),
            ('/-- Genuine finite original-source snapshot carrier', '#print axioms decode_encode_valid'),
        ],
    },
    'UnifiedLean.Source.NativePairClockLaw': {
        'namespace': 'UnifiedLean.Source.NativePairClockLaw',
        'prelude_end': '/-- Positive constant rates',
        'ranges': [('/-- Positive constant rates', '/-- The none coordinate')],
    },
    'UnifiedLean.Source.UniformizedSourceStep': None,
    'UnifiedLean.Source.SourceStepGeneratorBinding': {
        'namespace': 'UnifiedLean.Source.SourceStepGeneratorBinding',
        'prelude_end': 'local instance codeMeasurable',
        'ranges': [('local instance codeMeasurable', '/-- A real source merger')],
    },
    'UnifiedLean.Source.SourceFiniteProjection': {
        'namespace': 'UnifiedLean.Source.SourceFiniteProjection',
        'prelude_end': 'abbrev SelectedIndex ',
        'ranges': [('noncomputable def sourceTransition ', 'noncomputable def selectedTransition ')],
    },
    'UnifiedLean.Source.SourceGeneratorExponential': {
        'namespace': 'UnifiedLean.Source.SourceGeneratorExponential',
        'prelude_end': 'noncomputable def sourceGeneratorMatrix ',
        'ranges': [('noncomputable def sourceGeneratorMatrix ', 'noncomputable def selectedGeneratorMatrix ')],
    },
    'UnifiedLean.Source.SourcePoissonKernel': {
        'namespace': 'UnifiedLean.Source.SourcePoissonKernel',
        'prelude_end': 'noncomputable def sourceIteration ',
        'ranges': [
            ('noncomputable def sourceIteration ', 'noncomputable def selectedIteration '),
            ('noncomputable def globalClockRate ', 'noncomputable def selectedTimeKernel '),
        ],
    },
    'UnifiedLean.Source.SourcePoissonExponential': None,
    'UnifiedLean.Source.SourceActualHoldingClocks': {
        'namespace': 'UnifiedLean.Source.SourceActualHoldingClocks',
        'prelude_end': 'noncomputable def liveCard ',
        'ranges': [('noncomputable def liveCard ', 'lemma step_support_card_le ')],
    },
    'UnifiedLean.Source.SourceAncestralCompletion': {
        'namespace': 'UnifiedLean.Source.SourceAncestralCompletion',
        'prelude_end': 'def AncestralRoot ',
        'ranges': [('lemma choice_empty_of_terminal_card ', 'lemma ancestral_choice_exists ')],
    },
    'UnifiedLean.Source.SourceEpochRenewal': None,
    'G7SinglePopulationPolynomialKernel': None,
    'G7EffectiveSourceEnumeration': {
        'namespace': 'GProgram.G7.EffectiveSourceEnumeration',
        'prelude_end': 'instance boolEnumeration ',
        'ranges': [
            ('instance optionEnumeration ', 'instance treeCodeEnumeration '),
            ('/-- Equality is fieldwise;', 'instance snapshotEnumeration '),
            ('/-- Same inherited decoder,', 'theorem decode_eq '),
        ],
    },
    'G7EffectivePopulationCoefficients': None,
    'G7EffectiveCoefficientSupport': None,
}

# Only opens of omitted, unused namespaces are removed. Selected definitions,
# proof commands and original variable/section declarations are not rewritten.
OPEN_REPAIRS = {
    'SourceForestKingmanPopulationProjection': [
        ('open GProgram.SourceForest GProgram.SourceForestKingmanProjection\n',
         'open GProgram.SourceForest\n')],
    'UnifiedLean.Source.NativePairClockLaw': [
        ('open Nanuq.Source GProgram.G5 GProgram.G5.RouteHazard\n', 'open Nanuq.Source\n'),
        ('open UnifiedLean.Source.NativeParentRouting\n', '')],
    'UnifiedLean.Source.FiniteSourceSnapshot': [('open UnifiedLean.Source.SourceForestSilentPruning\n', '')],
    'UnifiedLean.Source.SourceStepGeneratorBinding': [
        ('open UnifiedLean.Source.SourceForestSilentPruning\n', ''),
        ('open UnifiedLean.Source.SourceForestGeneratorIntertwining\n', ''),
        ('open UnifiedLean.Source.SourceForestIntrinsicGenerator\n', '')],
    'UnifiedLean.Source.SourceFiniteProjection': [
        ('open UnifiedLean.Source.SourceForestSilentPruning\n', ''),
        ('open UnifiedLean.Source.SourceForestIntrinsicGenerator\n', '')],
    'UnifiedLean.Source.SourceGeneratorExponential': [('open UnifiedLean.Source.MatrixProjectionExponential\n', '')],
    'UnifiedLean.Source.SourceAncestralCompletion': [
        ('open UnifiedLean.Source.NativeParentRouting\n', ''),
        ('open UnifiedLean.Source.NativeIndependentPairMixture\n', ''),
        ('open UnifiedLean.Source.SourceFirstMarkDistribution\n', ''),
        ('open UnifiedLean.Source.SourceEmbeddedJumpLaw\n', ''),
        ('open UnifiedLean.Source.SourceNaturalInitialization\n', '')],
    'G7SinglePopulationPolynomialKernel': [('open UnifiedLean.G6.AncestralRateFree\n', '')],
    'G7EffectiveSourceEnumeration': [('open UnifiedLean.Source.SourceForestSilentPruning\n', '')],
}

STYLES = ''.join('set_option ' + name + ' false\n' for name in (
    'linter.unusedSectionVars', 'linter.unusedSimpArgs', 'linter.unusedVariables',
    'linter.style.haveILetI', 'linter.unusedTactic', 'linter.unnecessarySeqFocus',
    'linter.deprecated'))


def unique(text, token):
    if text.count(token) != 1:
        raise ValueError('UNIQUE_ORIGINAL_BOUNDARY_REQUIRED: ' + token)
    return text.index(token)


def selected(name, raw):
    text = raw.decode()
    spec = SPECS[name]
    ranges = []
    if spec is None:
        body = text
    else:
        first = unique(text, 'namespace ' + spec['namespace'] + '\n')
        prelude_end = unique(text, spec['prelude_end'])
        if first >= prelude_end:
            raise ValueError('INVALID_SCOPE_PRELUDE')
        pieces = [text[first:prelude_end]]
        previous = prelude_end
        for start, end in spec['ranges']:
            a, b = unique(text, start), unique(text, end)
            if a < previous or b <= a:
                raise ValueError('OVERLAPPING_OR_REORDERED_SOURCE_COMMANDS')
            part = text[a:b]
            ranges.append({'start': start, 'end_exclusive': end,
                           'start_line': text[:a].count('\n') + 1,
                           'end_line_exclusive': text[:b].count('\n') + 1,
                           'bytes': len(part.encode()), 'sha256': sha(part.encode())})
            pieces.append(part)
            previous = b
        closing = 'end ' + spec['namespace']
        if text.count(closing) != 1:
            raise ValueError('EXACT_ORIGINAL_NAMESPACE_END_REQUIRED')
        pieces.append(text[text.index(closing):text.index(closing) + len(closing)] + '\n')
        body = '\n'.join(pieces)
    omitted = []
    kept = []
    for line in body.splitlines(keepends=True):
        if line.startswith('import ') or re.fullmatch(r'\s*#print axioms [^\s]+\s*', line):
            omitted.append(line.strip())
        else:
            kept.append(line)
    body = ''.join(kept)
    changes = []
    for before, after in OPEN_REPAIRS.get(name, []):
        if body.count(before) != 1:
            raise ValueError('EXACT_UNUSED_OPEN_REPAIR_REQUIRED: ' + name)
        body = body.replace(before, after, 1)
        changes.append({'before': before, 'after': after})
    return body, {'module': name, 'original_bytes': len(raw), 'original_sha256': sha(raw),
                  'complete_module_body': spec is None, 'selected_ranges': ranges,
                  'open_only_repairs': changes, 'hoisted_imports_or_informational_prints': omitted,
                  'body_bytes': len(body.encode()), 'body_sha256': sha(body.encode())}


def declaration_inventory(text):
    """Review inventory only; it does not parse Lean or establish soundness."""
    frames, names = [], set()
    pattern = re.compile(r'^(?:@\[[^\n]*\]\s*)?(?:(?:noncomputable|private|protected|unsafe|local|scoped)\s+)*(?:def|abbrev|lemma|theorem|structure|inductive|instance)\s+([A-Za-z_][A-Za-z0-9_.]*)')
    for line in text.splitlines():
        match = re.fullmatch(r'(namespace|section)\s+([A-Za-z0-9_.]+)', line)
        if match:
            frames.append(match.groups())
            continue
        match = re.fullmatch(r'end(?:\s+([A-Za-z0-9_.]+))?\s*', line)
        if match:
            if frames and (match[1] is None or frames[-1][1] == match[1]):
                frames.pop()
            continue
        match = pattern.match(line)
        if match:
            prefix = '.'.join(name for kind, name in frames if kind == 'namespace')
            names.add((prefix + '.' if prefix else '') + match[1])
    return names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', type=Path, default=ROOT / 'native/prepared-master-and-encoded-support-project778')
    parser.add_argument('--output', type=Path, default=ROOT / 'lean/scoped-context/PopulationTableCertificate.lean')
    parser.add_argument('--source-map', type=Path, default=PUBLIC / 'SCOPED-POPULATION-CONTEXT-SOURCE-MAP.json')
    args = parser.parse_args()
    review_raw = checked(PUBLIC / 'POPULATION-DECLARATION-DEPENDENCY-REVIEW.json',
                         '30db4b6e0fe3f9bbd8d717566d17cc0d4581f218135c159a557d99a0ce86fb98')
    review = json.loads(review_raw)
    full = json.loads((PUBLIC / 'FULL-POPULATION-CONTEXT-SOURCE-MAP.json').read_bytes())
    if set(SPECS) != {r['module'] for r in review['selected_module_source_pins']} - {'Mathlib.Data.FinEnum'}:
        raise ValueError('EXACT_RETAINED_MODULE_SET_REQUIRED')
    order = [r for r in full['original_modules'] if r['module'] in SPECS]
    pieces, mapping, inventory = [], [], set()
    for index, pin in enumerate(order):
        raw = checked(args.project / 'source-store' / (pin['sha256'] + '.lean'), pin['sha256'])
        body, row = selected(pin['module'], raw)
        inventory.update(declaration_inventory(body))
        pieces.append('section ScopedPopulationModule' + str(index) + '\n' + STYLES + body
                      + '\nend ScopedPopulationModule' + str(index) + '\n')
        mapping.append(row)
    # The two original datatype deriving commands also own these generated names.
    generated = {
        'GProgram.SourceForest.instDecidableEqGenealogy': 'GProgram.SourceForest.Genealogy',
        'GProgram.SourceForest.instDecidableEqLocation': 'GProgram.SourceForest.Location',
    }
    coverage, missing = [], []
    for record in review['selected_declaration_records']:
        name = record['name']
        if record['module'] == 'Mathlib.Data.FinEnum':
            coverage.append({'name': name, 'source_command': 'IMPORTED_REVIEWED_MATHLIB_FINENUM'})
            continue
        candidates = [n for n in inventory if name == n or name.startswith(n + '.')]
        candidates += [parent for prefix, parent in generated.items()
                       if name == prefix or name.startswith(prefix + '.')]
        if not candidates:
            missing.append(name)
        else:
            coverage.append({'name': name, 'source_command': max(candidates, key=len)})
    if missing:
        raise ValueError('UNMAPPED_RETAINED_DECLARATIONS: ' + json.dumps(missing))
    wrapper = checked(PUBLIC / 'lean/hosted435/NativePopulationTableCertificate.lean',
                      next(r['selected_sha256'] for r in full['explicit_hosted_variants']
                           if r['module'] == 'NativePopulationTableCertificate'))
    wrapper_body = '\n'.join(line for line in wrapper.decode().splitlines()
                             if not line.startswith('import ')) + '\n'
    pieces.append('section ScopedPopulationCertificate\n' + STYLES + wrapper_body
                  + '\nend ScopedPopulationCertificate\n')
    output = ('\n'.join('import ' + name for name in full['external_imports'])
              + '\n\n' + '\n'.join(pieces)).encode()
    if re.search(rb'(?m)^\s*(?:#eval|run_cmd|initialize)\b|\bIO\.(?:FS|Process)\b', output):
        raise ValueError('UNSELECTED_SOURCE_RUNTIME_WRITER')
    if len(output) > 262144:
        raise ValueError('PROJECTION_EXCEEDS_ORIGINAL_CLIENT_SOURCE_GUARD')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(output)
    result = {
        'schema': 'scoped_original_population_certificate_context_v1',
        'classification': 'Verification/integration of the SAME physical endpoint with unchanged original definitions/proofs; no new kernel or theorem substitution.',
        'original_commit': full['original_commit'],
        'compiler_audit_raw_sha256': review['original_audit']['audit_raw_sha256'],
        'compiler_dependency_review_sha256': sha(review_raw),
        'original_modules_selected': mapping,
        'standard_library': full['hosted_standard_library_modules'],
        'external_imports': full['external_imports'],
        'retained_declaration_coverage': coverage,
        'coverage_is_inventory_not_elaboration': True,
        'source_namespace_variable_scope': 'Original per-module preludes and exact selected command groups; isolated outer sections. Explicit unused-open removals are recorded. No declaration/type/proof replacement.',
        'wrapper_sha256': sha(wrapper),
        'wrapper_proof_variant': 'Only the already checked polynomial_coefficient API proof repair from the existing full-context preparer.',
        'output_bytes': len(output), 'output_sha256': sha(output),
        'compiler_invoked': False, 'actual_native_table_checked': False,
        'status': 'SOURCE_PREPARED_UNVERIFIED',
        'scope': 'Exact generic admitted-Code table check and actual sourceTimeKernel endpoint, not captured Rust inputs, native/parser refinement, output origin or physical source/action coverage.'}
    args.source_map.parent.mkdir(parents=True, exist_ok=True)
    args.source_map.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'source_bytes': len(output), 'source_sha256': sha(output),
                      'original_modules': len(mapping), 'retained_decl_coverage': len(coverage),
                      'compiler_invoked': False, 'status': result['status']}))


if __name__ == '__main__':
    main()
