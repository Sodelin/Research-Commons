#!/usr/bin/env python3
"""Prepare exact bounded definition projections, without running Lean."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PINS = {
    'StrictAffineElimination': 'a0f597c021b761bfe79561eac03c19d754f93b4fa024ffb229ecaccdaeadf1f2',
    'GParity.Rational': 'bd054fff73f645f81fbe066daa94efa315efecac7480a8faaf9dc1611c7cff79',
    'GParity.Affine': 'db8fe686bd1bdd7ad95064ae3dbaf7666bce1ee8e1539ccb10bb9fb00d4c81f1',
    'GParity.Chart': '337d5e41153a356df2e9a8d8c7998d1f1d41bc56a331bcae10e8d2693768612a',
    'G6NaturalCellInverseRates': 'bd35c3f3f47ada67cceb9887059a3a9ed8662129bcab4dbe5d5ade07a377de5f',
    'NaturalCellAffineCompiler': 'b381a99725e1817b93a48a8356c282c08b6198d36794a2b5cd358f5368161ea0',
    'G6NaturalCellOrderedCompiler': '3e5672f9440c910693b5e952d3469ec3212f56b58e2949ff7c4b957e2a923ab2',
}


def checked(name, source_store):
    digest = PINS[name]
    path = source_store/(digest+'.lean')
    body = path.read_text()
    if hashlib.sha256(body.encode()).hexdigest() != digest:
        raise ValueError('ORIGINAL_SOURCE_CHANGED: '+name)
    return body


def between(body, first, last):
    if body.count(first) != 1 or body.count(last) != 1:
        raise ValueError('EXACT_PROJECTION_BOUNDARY_REQUIRED')
    return body[body.index(first):body.index(last)]


def no_imports(body):
    return '\n'.join(line for line in body.splitlines()
                     if not line.startswith('import '))+'\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-store',type=Path,required=True,
        help='The separately prepared, hash-verified original module source store.')
    args = parser.parse_args()
    sources = {name:checked(name,args.source_store.resolve()) for name in PINS}
    parts = [no_imports(sources[name]) for name in
             ('StrictAffineElimination','GParity.Rational','GParity.Affine','GParity.Chart')]
    inverse = sources['G6NaturalCellInverseRates']
    interval = between(inverse, 'structure RationalBound where', 'theorem interval_div_iff')
    comparison = between(inverse, 'inductive AgeComparison\n', 'structure AgeConstraint (V : Type*)')
    parts.append('namespace UnifiedLean.G6.NaturalCellInverseRates\n'+
                 interval+comparison+'\nend UnifiedLean.G6.NaturalCellInverseRates\n')
    affine = between(sources['NaturalCellAffineCompiler'],
        'namespace UnifiedLean.G6.NaturalCellAffineCompiler\n', 'variable {V E X I C : Type*}')
    omitted_opens = [
        'open Nanuq.Source GProgram.G5',
        'open UnifiedLean.Source.NativePairClockLaw',
        'open UnifiedLean.Source.NativeParentRouting',
        'open UnifiedLean.Source.NativeIndependentPairMixture']
    for line in omitted_opens:
        if affine.count(line+'\n') != 1:
            raise ValueError('OPEN_PROJECTION_CHANGED')
        affine = affine.replace(line+'\n','')
    parts.append(affine+'\nend UnifiedLean.G6.NaturalCellAffineCompiler\n')
    ordered = sources['G6NaturalCellOrderedCompiler']
    primitives = between(ordered,'def comparisonList {n : ℕ}', 'theorem flatMap_toFinset_univ')
    encoders = between(ordered,'def encodeRow {n : ℕ}', 'theorem decodeVector_ofFn')
    parts.append('namespace UnifiedLean.G6.NaturalCellOrderedCompiler\n'
        'open UnifiedLean.G6.StrictAffineElimination\n'
        'open UnifiedLean.G6.NaturalCellInverseRates\n'
        'open UnifiedLean.G6.NaturalCellAffineCompiler\n'+primitives+encoders+
        '\nend UnifiedLean.G6.NaturalCellOrderedCompiler\n')
    proof = (ROOT/'lean/NativeCellFormReflection.lean').read_bytes()
    parts.append(no_imports(proof.decode()))
    imports = ['Mathlib.Data.Finset.Max','Mathlib.Data.Rat.Cast.Order',
               'Mathlib.Tactic','Init.Data.Rat','Std']
    body = '\n'.join('import '+name for name in imports)+'\n\n'+'\n'.join(parts)
    destination = ROOT/'lean/OnlineNativeCellFormReflection.lean'
    destination.write_text(body)
    mapping = {'kind':'exact_existing_definition_projection_for_form_reflection',
        'original_sources':PINS,'omitted_unused_open_lines':omitted_opens,
        'projected_sections':['full strict/rat/affine/CHART value bodies',
            'exact rational interval/comparison definitions',
            'exact typed affine forms/rows before physical bank declarations',
            'exact ordered comparison/scaled and row-encoding definitions'],
        'authored_source_sha256':hashlib.sha256(proof).hexdigest(),
        'virtual_source_sha256':hashlib.sha256(body.encode()).hexdigest(),
        'full_physical_import_elaboration':False}
    (ROOT/'lean/NativeCellFormReflection-SOURCE-MAP.json').write_text(
        json.dumps(mapping,indent=2)+'\n')
    print(json.dumps({'source_only_projection_bytes':len(body.encode()),
        'compiler_invoked':False,'full_physical_import_elaboration':False}))


if __name__ == '__main__':
    main()
