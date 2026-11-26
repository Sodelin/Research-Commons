#!/usr/bin/env python3
"""Select the existing sparse-row caller over the checked physical certificate.

Exact original definitions/proofs are reused. No state/kernel/fibre engine,
source factory, parser or native emitter is introduced by this source preparer.
"""
import json
from pathlib import Path
from prepare_population_scoped_context import sha, checked, unique

ROOT = Path(__file__).resolve().parent
PUBLIC = ROOT / 'public-packet' if (ROOT / 'public-packet').is_dir() else ROOT
STORE = ROOT / 'native/prepared-master-and-encoded-support-project778/source-store'


def selected(digest, start, end, replacements):
    raw = checked(STORE / (digest + '.lean'), digest)
    text = raw.decode()
    a, b = unique(text, start), unique(text, end)
    if a >= b:
        raise ValueError('EXACT_ORIGINAL_COMMAND_ORDER_REQUIRED')
    body = text[a:b]
    edits = []
    for before, after in replacements:
        if body.count(before) != 1:
            raise ValueError('EXACT_UNUSED_OPEN_BOUNDARY_REQUIRED')
        body = body.replace(before, after, 1)
        edits.append({'before': before, 'after': after})
    return body, {'original_sha256': digest, 'original_bytes': len(raw),
        'start': start, 'end_exclusive': end, 'start_line': text[:a].count('\n') + 1,
        'end_line_exclusive': text[:b].count('\n') + 1,
        'unused_open_only_edits': edits, 'selected_body_bytes': len(body.encode()),
        'selected_body_sha256': sha(body.encode())}


def main():
    base = checked(PUBLIC / 'lean/scoped-context/PopulationTableCertificate.lean',
        '801504467b7bf1440bdf9ab4d9d052790724605541838223956e4367d2842d35')
    pieces, mapping = [base.decode()], []
    common_opens = [
        ('open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCopyCarrierTransport\n', ''),
        ('open GProgram.G7.WholeAncestorPanelCode GProgram.G7.PopulationForestReassembly\n', ''),
        ('open GProgram.G7.FiniteForestReassembly ', 'open '),
    ]
    body, pin = selected(
        'fc3a6ccca93b085f42b3b6b403094922cabc87b5b92b551a982f958438472ec2',
        'namespace GProgram.G7.FullEpochPolynomial\n', 'noncomputable def evaluate ',
        common_opens + [('open G1ActualJointEpoch DotG6.ActualPopulationPanelSplit\n', '')])
    pieces.append('\nsection CertifiedRowsOriginalSurvival\n' + body +
        'end GProgram.G7.FullEpochPolynomial\nend CertifiedRowsOriginalSurvival\n')
    mapping.append({'module': 'G7FullEpochPolynomial', **pin})
    body, pin = selected(
        '85bed5b975ebb09a4042952aa486459d5cf422903d4356ac049d6d681b891994',
        'namespace GProgram.G7.EffectiveFullEpochCoefficients\n',
        'variable {Copy : Type uC}',
        common_opens + [('open DotG6.ActualPopulationPanelSplit\n', '')])
    pieces.append('\nsection CertifiedRowsOriginalSparse\n' + body +
        'end GProgram.G7.EffectiveFullEpochCoefficients\nend CertifiedRowsOriginalSparse\n')
    mapping.append({'module': 'G7EffectiveFullEpochCoefficients', **pin})
    body, pin = selected(
        '31644d88dcdebdeb2d2bce8f834fcb5a9925458bcf6e7868e262dd0484a79ad1',
        'namespace GProgram.G7.SparseRowProducts\n', 'def multiplyRows ',
        [('open GProgram.G7.PopulationSelectedSupport\n', '')])
    pieces.append('\nsection CertifiedRowsOriginalReader\n' + body +
        'end GProgram.G7.SparseRowProducts\nend CertifiedRowsOriginalReader\n')
    mapping.append({'module': 'G7SparseRowProducts', **pin})
    caller = checked(PUBLIC / 'lean/proposals/G7CertifiedPopulationRows.lean',
        '9b1dd5f8660ea516383884ff1c6a14d713543a1cca3eb1fb23c26b6c820f7663')
    text = caller.decode()
    body = text[unique(text, 'namespace Astra.CertifiedPopulationRows\n'):]
    pieces.append('\nsection ExistingCertifiedPopulationRowsCaller\nopen scoped NNReal\n' +
        body + '\nend ExistingCertifiedPopulationRowsCaller\n')
    document = ''.join(pieces).encode()
    path = PUBLIC / 'lean/scoped-context/CertifiedPopulationRows.lean'
    path.write_bytes(document)
    result = {'schema': 'certified_population_rows_context_source_map_v1',
        'classification': 'Verification/integration of an already supplied sparse-row caller; original population/fibre mathematics is reused.',
        'checked_physical_base_bytes': len(base), 'checked_physical_base_sha256': sha(base),
        'unchanged_physical_base_is_literal_prefix': document.startswith(base),
        'original_modules': mapping,
        'unchanged_caller_source_sha256': sha(caller), 'unchanged_caller_body_sha256': sha(body.encode()),
        'scope_only_addition': 'open scoped NNReal before the unchanged caller, reusing the prior accepted context correction.',
        'source': str(path.relative_to(PUBLIC)), 'source_bytes': len(document), 'source_sha256': sha(document),
        'actual_native_table_or_capture': False, 'native_writer_controller': 'UNBOUND'}
    (PUBLIC / 'CERTIFIED-POPULATION-ROWS-SOURCE-MAP.json').write_text(
        json.dumps(result, ensure_ascii=False, indent=2) + '\n')
    print(json.dumps({'state': 'SOURCE_PREPARED_NOT_CHECKED', 'bytes': len(document),
        'sha256': sha(document), 'unchanged_physical_base': document.startswith(base),
        'original_caller_body_unchanged': True}))


if __name__ == '__main__':
    main()
