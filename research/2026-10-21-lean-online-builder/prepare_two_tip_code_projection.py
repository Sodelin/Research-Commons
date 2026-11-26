#!/usr/bin/env python3
"""Project one retained concrete source use-site without its five evaluations."""
import hashlib
import json
from pathlib import Path
from prepare_chart_form_projection import between, no_imports

ROOT = Path(__file__).resolve().parent
FIXTURE_SHA = '1d7e4d7509022405182bd8c98e98e59d73d013899b4cecd29d55a854a2972bfb'
BASE_SHA = '33d7779d1cdf7e69172c6dd9d3b13863e43534e5b1d124411418e0496402aa2c'

def sha(raw): return hashlib.sha256(raw).hexdigest()

def main():
    original = (ROOT/'intake/modules/G6TwoTipChartFixture.lean').read_bytes()
    base = (ROOT/'lean/OnlineOriginalCodeChartReceiver.lean').read_bytes()
    if sha(original) != FIXTURE_SHA:
        raise ValueError('RETAINED_FIXTURE_CHANGED')
    if sha(base) != BASE_SHA:
        raise ValueError('CHECKED_RECEIVER_CHANGED')
    text = original.decode()
    selected = ('namespace UnifiedLean.G6.TwoTipChartFixture\n'
        'open Nanuq.Source GProgram.G5\n'
        'open UnifiedLean.Source.NativeParentRouting\n' +
        between(text, 'def graph : EdgeGraph', 'def encodeVar : BankVar') + '\n' +
        between(text, 'def nativeSource : GParity.Chart.Source', 'theorem affineRow_ext') +
        '\nend UnifiedLean.G6.TwoTipChartFixture\n')
    proof = (ROOT/'lean/TwoTipOriginalCodeReceiver.lean').read_bytes()
    admission = (ROOT/'intake/modules/G7OriginalAdmission.lean').read_bytes()
    if sha(admission) != '16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c':
        raise ValueError('ORIGINAL_ADMISSION_CHANGED')
    cut_child = ('namespace GProgram.G7.OriginalAdmission\n'
        'open Nanuq.Source\nopen GProgram.G7.OriginalFiniteEncoding\n'
        'variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]\n' +
        between(admission.decode(), 'def CutChild (c : Code X ID)', 'instance decidableCutChild') +
        '\nend GProgram.G7.OriginalAdmission\n')
    if any(command in selected for command in ('#eval', '#print', 'run_cmd', 'IO.FS')):
        raise ValueError('UNSELECTED_EVALUATION_OR_WRITER')
    declarations = ('import G6NaturalCellOrderedCompiler\nimport GParity.Chart\n'
        'import Mathlib.Tactic.FinCases\n\n' + selected).encode()
    (ROOT/'lean/TwoTipSourceDeclarations.lean').write_bytes(declarations)
    raw = ('import Mathlib.Tactic.FinCases\n' + base.decode() + '\n' +
           cut_child + '\n' + selected + '\n' + no_imports(proof.decode())).encode()
    if len(raw) > 258000:
        raise ValueError('EXISTING_LANE_BYTE_LIMIT')
    (ROOT/'lean/OnlineTwoTipOriginalCodeReceiver.lean').write_bytes(raw)
    (ROOT/'lean/TwoTipOriginalCodeReceiver-SOURCE-MAP.json').write_text(json.dumps({
        'kind': 'retained_two_tip_source_and_literal_code_receiver_use_site',
        'retained_fixture_sha256': sha(original),
        'retained_fixture_git_blob': 'aa09622666e50184165af2c1dbf4978129a0b17a',
        'previous_checked_receiver_sha256': sha(base),
        'original_admission_source_sha256': sha(admission),
        'cut_child_projected_definition_sha256': sha(cut_child.encode()),
        'selected_retained_sections': ['graph through noHybrid',
            'nativeSource/nativeInput/nativeSource_valid'],
        'selected_retained_body_sha256': sha(selected.encode()),
        'declarations_module_sha256': sha(declarations),
        'all_five_original_evaluations_excluded': True,
        'authored_sha256': sha(proof), 'virtual_bytes': len(raw),
        'virtual_sha256': sha(raw), 'compiler_invoked_by_preparation': False,
        'parser_native_execution_or_origin_acceptance': False}, indent=2)+'\n')
    print(json.dumps({'source_only_bytes': len(raw), 'virtual_sha256': sha(raw),
        'excluded_evaluations': 5, 'compiler_invoked': False}))

if __name__ == '__main__': main()
