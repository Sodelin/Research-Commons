#!/usr/bin/env python3
"""Check the existing exporter's source boundary using retained declarations.

This selects original commands and a literal field-target use site. It does
not run Rust, render a native table, create a source factory or claim native
input provenance. The old original-source fixture supplies the source/input.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PUBLIC = ROOT / 'public-packet' if (ROOT / 'public-packet').is_dir() else ROOT
STORE = ROOT / 'native/prepared-master-and-encoded-support-project778/source-store'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def original(digest):
    path = STORE / (digest + '.lean')
    if not path.exists():
        path = ROOT / 'intake/reused-source' / (digest + '.lean')
    raw = path.read_bytes()
    if sha(raw) != digest:
        raise ValueError('ORIGINAL_SOURCE_CHANGED')
    return raw.decode()


def part(text, start, end):
    if text.count(start) != 1 or text.count(end) != 1:
        raise ValueError('EXACT_ORIGINAL_BOUNDARY_REQUIRED')
    a, b = text.index(start), text.index(end)
    if a >= b:
        raise ValueError('REVERSED_ORIGINAL_COMMANDS')
    return text[a:b], {'start': start, 'end_exclusive': end,
        'start_line': text[:a].count('\n') + 1,
        'end_line_exclusive': text[:b].count('\n') + 1,
        'bytes': len(text[a:b].encode()), 'sha256': sha(text[a:b].encode())}


def main():
    base_path = PUBLIC / 'lean/scoped-context/PopulationTableCertificate.lean'
    base = base_path.read_bytes()
    if sha(base) != '801504467b7bf1440bdf9ab4d9d052790724605541838223956e4367d2842d35':
        raise ValueError('CHECKED_PHYSICAL_BASE_REQUIRED')
    exporter = (ROOT / 'intake/rust/g7_population_certificate-0874c13e.rs').read_bytes()
    if sha(exporter) != '19967b34c4ba2a4b55cb4c93745ed7efd573d2e10edebb67274603d01f78404c':
        raise ValueError('EXACT_RETAINED_EXPORTER_REQUIRED')
    if 'out.put(" := by decide\\n\\ntheorem taxa_exact : N.leaf = ")?;' not in exporter.decode():
        raise ValueError('EXACT_EMITTED_FIELD_TARGET_REQUIRED')

    pieces, mappings = [base.decode()], []
    reach_sha = '25673c4d0a0ec0891ff204ff79c018d8e9ad1971962183e0a7332b6d709d2a35'
    reach = original(reach_sha)
    reach_body, reach_range = part(reach, 'namespace GProgram.G7.FiniteReachability\n',
                                  '#print axioms reached_iff')
    pieces.append('\nsection ExporterReachability\n' + reach_body +
                  'end GProgram.G7.FiniteReachability\nend ExporterReachability\n')
    mappings.append({'module': 'G7FiniteReachability', 'original_sha256': reach_sha,
                     'selected_ranges': [reach_range]})

    enum_sha = '6dabfdee6e47169a0135bc26523230213785338538c8179fc67d3cbc64cc3138'
    enum = original(enum_sha)
    prelude, pr = part(enum, 'namespace GProgram.G7.EffectiveSourceEnumeration\n',
                       'instance boolEnumeration ')
    prelude = prelude.replace('open UnifiedLean.Source.SourceForestSilentPruning\n', '')
    well, wr = part(enum, 'instance wellLabelledDecidable ', 'abbrev AdmissibleTreeCode ')
    deciders, dr = part(enum, 'def forestValidDecidable ',
                        '/-- The original admitted snapshot subtype is enumerated,')
    pieces.append('\nsection ExporterValidityDeciders\n' + prelude + well + deciders +
                  'end GProgram.G7.EffectiveSourceEnumeration\nend ExporterValidityDeciders\n')
    mappings.append({'module': 'G7EffectiveSourceEnumeration', 'original_sha256': enum_sha,
        'selected_ranges': [pr, wr, dr],
        'only_prelude_edit': 'Remove unused open of omitted SourceForestSilentPruning.'})

    source_sha = '1afa303d7ee2f28fba18fa719139acbf701ac24e10b4f00365cb2c6e69193a19'
    source = original(source_sha)
    source_body, sr = part(source, 'namespace UnifiedLean.G6.TwoTipChartFixture\n',
                           'def nativeSource ')
    source_body = source_body.replace('open Nanuq.Source GProgram.G5\n', 'open Nanuq.Source\n')
    source_body = source_body.replace('open UnifiedLean.Source.NativeParentRouting\n', '')
    pieces.append('\nsection RetainedOriginalTwoTipSource\n' + source_body +
                  'end UnifiedLean.G6.TwoTipChartFixture\nend RetainedOriginalTwoTipSource\n')
    mappings.append({'module': 'G6TwoTipChartFixture', 'original_sha256': source_sha,
        'selected_ranges': [sr],
        'only_prelude_edits': 'Remove unused G5/NativeParentRouting opens; original source and proofs unchanged.',
        'excluded': 'Unrelated native CHART fixture data.'})

    fixture_sha = '7544fc1cbe13a340a858ee17a73985881278957ed146ff7f27d5fc80618c52cc'
    fixture = original(fixture_sha)
    fixture_body, fr = part(fixture, 'namespace UnifiedLean.G7.OriginalPopulationFixture\n',
                            '/-- A valid entering forest with a carried subtree')
    pieces.append('\nsection RetainedPopulationInput\n' + fixture_body +
                  'end UnifiedLean.G7.OriginalPopulationFixture\nend RetainedPopulationInput\n')
    mappings.append({'module': 'G7OriginalPopulationFixture', 'original_sha256': fixture_sha,
        'selected_ranges': [fr], 'excluded': 'Coefficient producer, serializer, run/main and IO.'})

    # These are proof-target compatibility checks for the RETAINED source.
    # They are not output claimed to have been rendered by the unexecuted Rust.
    use_site = '''
namespace Astra.PopulationExporterSourceBoundary
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.EffectiveSourceEnumeration
open UnifiedLean.G7.OriginalPopulationFixture

private abbrev N : RootedBinary (Fin 3) (Fin 2) (Fin 2) :=
  UnifiedLean.G6.TwoTipChartFixture.source

theorem root_exact : N.root = ⟨0, by decide⟩ := by decide

theorem edge_sources_exact : N.graph.source =
    (fun i => if i.val = 0 then ⟨0, by decide⟩ else ⟨0, by decide⟩) := by decide

theorem edge_targets_exact : N.graph.target =
    (fun i => if i.val = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩) := by decide

theorem taxa_exact : N.leaf =
    (fun i => if i.val = 0 then ⟨1, by decide⟩ else ⟨2, by decide⟩) := by decide

/-- The actual retained source-valid input constructor, without running its producer. -/
theorem retained_input_source_valid (n : Nat) (i : Option (Fin 2))
    (register : Fin 3 → Bool) : SourceValid N (sample n i) (initialState n i register) :=
  initialState_sourceValid n i register

/-- The exporter's existing executable decider at that same original input. -/
def retained_input_decider (n : Nat) (i : Option (Fin 2))
    (register : Fin 3 → Bool) :
    Decidable (SourceValid N (sample n i) (initialState n i register)) :=
  sourceValidDecidable N (sample n i) (initialState n i register)

end Astra.PopulationExporterSourceBoundary
'''
    pieces.append(use_site)
    document = ''.join(pieces).encode()
    path = PUBLIC / 'lean/scoped-context/PopulationExporterSourceBoundary.lean'
    path.write_bytes(document)
    mapping = {'schema': 'population_exporter_source_boundary_projection_v1',
        'classification': 'Verification of existing source/input/decider and emitted field-target compatibility; not native rendering or a new fixture.',
        'checked_physical_base_sha256': sha(base), 'checked_physical_base_bytes': len(base),
        'unchanged_base_is_literal_prefix': document.startswith(base),
        'retained_exporter_sha256': sha(exporter),
        'retained_exporter_successor_commit': '4ac6aa8565ec8aa2bac1d5dc4b3d31af64e86859',
        'original_modules': mappings, 'authored_use_site_sha256': sha(use_site.encode()),
        'source_bytes': len(document), 'source_sha256': sha(document),
        'not_claimed': ['Rust compilation/execution', 'Actual native table/capture',
                        'Rendered native proof document', 'Installed original imports/objects',
                        'Runtime proof/result origin', 'Full source/action coverage'],
        'native_writer_controller': 'UNBOUND'}
    (PUBLIC / 'POPULATION-EXPORTER-SOURCE-BOUNDARY-SOURCE-MAP.json').write_text(
        json.dumps(mapping, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'state': 'SOURCE_PREPARED_NOT_CHECKED', 'source': str(path.relative_to(ROOT)),
        'bytes': len(document), 'sha256': sha(document),
        'checked_base_unchanged': document.startswith(base), 'native_executed': False}))


if __name__ == '__main__':
    main()
