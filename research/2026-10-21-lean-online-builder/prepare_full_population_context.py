#!/usr/bin/env python3
"""Retain the COMPLETE original row-certificate dependency context for hosted Lean.

No theorem extraction, compiler, native process, fixture producer or object reuse.
All original declarations remain; only imports/informational prints are hoisted
and the previously checked hosted API proof variants are explicitly selected.
"""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parent
PUBLIC = ROOT / 'public-packet'
PROJECT = ROOT / 'native/prepared-master-and-encoded-support-project778'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def checked(path, expected):
    raw = path.read_bytes()
    if sha(raw) != expected:
        raise ValueError('SOURCE_IDENTITY_CHANGED: ' + path.name)
    return raw


def main():
    graph_raw = (PROJECT / 'DEPENDENCY-GRAPH.json').read_bytes()
    if sha(graph_raw) != 'e3c299e538b6d956d5562243140d246246f121edcacc1c1bea9bd23bbb18811c':
        raise ValueError('EXACT_SOURCE_CONTEXT_REQUIRED')
    modules = next(iter(json.loads(graph_raw)['targets'].values()))['modules']
    order, seen = [], set()

    def visit(name):
        if name in seen:
            return
        for dep in modules[name]['imports']:
            if dep in modules:
                visit(dep)
        seen.add(name)
        order.append(name)

    visit('G7EffectiveCoefficientSupport')
    prior_api = json.loads((ROOT / 'lean/hosted435/SOURCE-VARIANTS.json').read_bytes())['variants']
    originals, inputs, changes, libraries = [], [], [], []
    for name in order:
        raw = checked(PROJECT / 'source-store' / (modules[name]['sha256'] + '.lean'),
                      modules[name]['sha256'])
        originals.append({'module': name, 'bytes': len(raw), 'sha256': sha(raw)})
        if name == 'Mathlib.Data.FinEnum':
            hosted_library = checked(ROOT / 'intake/upstream/Mathlib-56a005-Data-FinEnum.lean',
                '9a7bffed9df4a55b650ef196d70fc5f5188f97c522445fc93e0c66dd4776fdc5')
            libraries.append({'module': name, 'original_sha256': sha(raw),
                'hosted_source_sha256': sha(hosted_library),
                'mathlib_revision': '56a005855ea17e0b0958f73ec801ae140b0a1679',
                'reason': 'Use the actual standard-library module at the checked service revision; its module/public-import header cannot be nested in a flattened section. Full old/new source difference is retained; computational definitions are unchanged.'})
            continue
        if name in ('G5FairSelectorMoments', 'G4PathResolvedMeasurement'):
            record = prior_api[name]
            selected = checked(ROOT / record['path'], record['sha256'])
            changes.append({'module': name, 'original_sha256': sha(raw),
                            'selected_sha256': sha(selected),
                            'reason': 'Unchanged explicit API variant from the already checked complete admission component.'})
            raw = selected
        inputs.append((name, raw))
    if len(order) != 92 or sum(x['bytes'] for x in originals) != 643093:
        raise ValueError('RETAINED_COMPLETE_CLOSURE_CHANGED')

    original = checked(ROOT / 'lean/NativePopulationTableCertificate.lean',
        '4a0b8b00f672d39fc74363246b2935876ebc92c9d1c46e46715e572b689a3be6')
    rejected = checked(ROOT / 'lean/proposals/rejected/PopulationCoefficientProjection-r0.lean',
        '4febe046c4c7ed900adc84e391dcb7a4530dc5bedebe9395e275e3cae4d5a899')
    accepted = checked(ROOT / 'lean/proposals/PopulationCoefficientProjection.lean',
        'ea3b6538a10be5ba470d372a30a70bc6e7f53b8b98880501c4d90f5b7bc3b15c')
    start, end = b'lemma polynomial_coefficient ', b'lemma coefficient_zero_of_absent '

    def proof_block(raw):
        return raw[raw.index(start):raw.index(end)]

    if proof_block(original) != proof_block(rejected):
        raise ValueError('EXACT_PRIOR_PROOF_HUNK_REQUIRED')
    hosted = original.replace(proof_block(original), proof_block(accepted), 1)
    hosted_dir = ROOT / 'lean/hosted435'
    (hosted_dir / 'NativePopulationTableCertificate.lean').write_bytes(hosted)
    public_hosted = PUBLIC / 'lean/hosted435/NativePopulationTableCertificate.lean'
    public_hosted.parent.mkdir(parents=True, exist_ok=True)
    public_hosted.write_bytes(hosted)
    changes.append({'module': 'NativePopulationTableCertificate',
                    'original_sha256': sha(original), 'selected_sha256': sha(hosted),
                    'reason': 'Only polynomial_coefficient proof reuses the exact already checked ea3b6538 hosted API repair; all definitions and other proofs unchanged.'})
    inputs.append(('NativePopulationTableCertificate', hosted))

    names = {name for name, _ in inputs}
    external = [row['module'] for row in libraries]
    pieces, source_map = [], []
    for number, (name, raw) in enumerate(inputs):
        text = raw.decode()
        if re.search(r'(?m)^\s*(?:#eval|run_cmd|initialize)\b|\bIO\.(?:FS|Process)\b', text):
            raise ValueError('UNSELECTED_RUNTIME_OR_EVALUATION: ' + name)
        body, omitted = [], []
        for line_number, line in enumerate(text.splitlines(keepends=True), 1):
            if line.startswith('import '):
                for dep in line.strip().split()[1:]:
                    if dep not in names and dep not in external:
                        external.append(dep)
                body.append('\n' if line.endswith('\n') else '')
            elif re.fullmatch(r'\s*#print axioms [^\s]+\s*', line):
                omitted.append({'line': line_number, 'command': line.strip()})
                body.append('\n' if line.endswith('\n') else '')
            else:
                body.append(line)
        selected = ''.join(body)
        styles = ('set_option linter.unusedSectionVars false\n'
                  'set_option linter.unusedSimpArgs false\n'
                  'set_option linter.unusedVariables false\n'
                  'set_option linter.style.haveILetI false\n'
                  'set_option linter.unusedTactic false\n'
                  'set_option linter.unnecessarySeqFocus false\n'
                  'set_option linter.deprecated false\n')
        pieces.append('section FullContextModule' + str(number) + '\n' + styles + selected
                      + '\nend FullContextModule' + str(number) + '\n')
        source_map.append({'module': name, 'selected_bytes': len(raw),
                           'selected_sha256': sha(raw), 'body_bytes': len(selected.encode()),
                           'body_sha256': sha(selected.encode()),
                           'omitted_informational_prints': omitted})
    document = ('\n'.join('import ' + name for name in external) + '\n\n'
                + '\n'.join(pieces)).encode()
    if len(document) > 1048576:
        raise ValueError('FULL_CONTEXT_EXCEEDS_EXPLICIT_ONE_MIB_BOUND')
    destination = ROOT / 'lean/full-context'
    destination.mkdir(parents=True, exist_ok=True)
    (destination / 'PopulationTableCertificate.lean').write_bytes(document)
    public_dest = PUBLIC / 'lean/full-context'
    public_dest.mkdir(parents=True, exist_ok=True)
    (public_dest / 'PopulationTableCertificate.lean').write_bytes(document)
    mapping = {'schema': 'complete_population_certificate_context_v1',
               'original_commit': '1138a5b1a281caa00b38e0976db95b586938754b',
               'original_root': 'G7EffectiveCoefficientSupport',
               'original_modules': originals, 'original_module_count': len(order),
               'original_source_bytes': sum(x['bytes'] for x in originals),
               'selected_sources': source_map, 'explicit_hosted_variants': changes,
               'hosted_standard_library_modules': libraries,
               'external_imports': external, 'virtual_bytes': len(document),
               'virtual_sha256': sha(document), 'declarations_omitted': [],
               'source_transform': 'Only imports and unselected informational axiom prints are hoisted; all authored module declarations/comments retained inside isolated sections. The original borrowed FinEnum library is imported at the exact reviewed hosted revision instead of flattening its header.',
               'suppressed_style_or_deprecation_linters': [
                   'linter.unusedSectionVars', 'linter.unusedSimpArgs',
                   'linter.unusedVariables', 'linter.style.haveILetI',
                   'linter.unusedTactic', 'linter.unnecessarySeqFocus', 'linter.deprecated'],
               'errors_or_unsafe_warnings_suppressed': False,
               'compiler_invoked_by_preparer': False, 'native_context_changed': False,
               'scope': 'Full imported mathematical certificate context, not a literal native output or parser/refinement proof.'}
    (PUBLIC / 'FULL-POPULATION-CONTEXT-SOURCE-MAP.json').write_text(json.dumps(mapping, indent=2) + '\n')
    print(json.dumps({'original_modules': len(order), 'selected_modules': len(inputs),
                      'original_source_bytes': mapping['original_source_bytes'],
                      'virtual_bytes': len(document), 'virtual_sha256': sha(document),
                      'explicit_hosted_variants': len(changes), 'compiler_invoked': False}))


if __name__ == '__main__':
    main()
