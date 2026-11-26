#!/usr/bin/env python3
"""Prepare exact source/data/compiler projections; no compiler or solver runs."""
import argparse
import hashlib
import json
from pathlib import Path
from prepare_chart_form_projection import PINS, between, checked, no_imports

ROOT = Path(__file__).resolve().parent
EXTRA_PINS = {
    'SourceNetwork':'0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7',
    'UnifiedLean.Source.NativeParentRouting':'300d7216193e945ca26161535c1bc2ba75a128fe5c075b6a3567bbda66bfe0b6',
    'G6WireAffineRefinement':'d5131590649cc79ff7337b35aa0dbca44964585c8b72c25af812b05d84b78737',
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-store',type=Path,required=True)
    args=parser.parse_args()
    original={name:checked(name,args.source_store) for name in PINS}
    for name,digest in EXTRA_PINS.items():
        raw=(args.source_store/(digest+'.lean')).read_bytes()
        if sha(raw)!=digest:raise ValueError('ORIGINAL_SOURCE_CHANGED')
        original[name]=raw.decode()
    form=(ROOT/'lean/OnlineNativeCellFormReflection.lean').read_bytes()
    if sha(form)!='7ce2eed4770e527b335a9cbee408ff5bcdb6dc8734ad40e2895182d9faa6bad7':
        raise ValueError('CHECKED_FORM_COMPONENT_CHANGED')
    parts=[form.decode(),no_imports(original['SourceNetwork'])]
    parent=original['UnifiedLean.Source.NativeParentRouting']
    hybrid='abbrev Hybrid (N : RootedBinary V E X) := {v : V // N.graph.IsHybrid v}'
    if parent.count(hybrid)!=1:raise ValueError('HYBRID_DECLARATION_CHANGED')
    parts.append('namespace UnifiedLean.Source.NativeParentRouting\nopen Nanuq.Source\n'
        'variable {V E X : Type*}\nvariable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]\n'+hybrid+
        '\nend UnifiedLean.Source.NativeParentRouting\n')
    inverse=original['G6NaturalCellInverseRates']
    parts.append('namespace UnifiedLean.G6.NaturalCellInverseRates\n'+
        between(inverse,'inductive AgeAtom (V : Type*)','/-- The identical bank')+
        between(inverse,'structure AgeConstraint (V : Type*)','variable {C : Type*}')+
        '\nend UnifiedLean.G6.NaturalCellInverseRates\n')
    affine=original['NaturalCellAffineCompiler']
    parts.append('namespace UnifiedLean.G6.NaturalCellAffineCompiler\nopen Nanuq.Source\n'
        'open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.NaturalCellInverseRates\n'
        'open UnifiedLean.Source.NativeParentRouting\n'+
        between(affine,'variable {V E X I C : Type*}','@[simp] theorem ageForm_eval')+
        between(affine,'def chronologyRows (c : AgeConstraint V)','@[simp] theorem chronologyRows_holds')+
        between(affine,'def compileCell (chronology : C → AgeConstraint V)','def BankConditions')+
        '\nend UnifiedLean.G6.NaturalCellAffineCompiler\n')
    wire=original['G6WireAffineRefinement']
    parts.append('namespace UnifiedLean.G6.WireAffineRefinement\n'
        'open UnifiedLean.G6.StrictAffineElimination\n'+
        between(wire,'def decodeVector (n : ℕ)','theorem ofFn_decodeVector')+
        '\nend UnifiedLean.G6.WireAffineRefinement\n')
    ordered=original['G6NaturalCellOrderedCompiler']
    parts.append('namespace UnifiedLean.G6.NaturalCellOrderedCompiler\nopen Nanuq.Source\n'
        'open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.NaturalCellInverseRates\n'
        'open UnifiedLean.G6.NaturalCellAffineCompiler UnifiedLean.G6.WireAffineRefinement\n'
        'open UnifiedLean.Source.NativeParentRouting\n'+
        between(ordered,'theorem flatMap_toFinset_univ','def encodeRow {n : ℕ}')+
        between(ordered,'theorem decodeVector_ofFn {n : ℕ}','/-- Any actual native positive')+
        '\nend UnifiedLean.G6.NaturalCellOrderedCompiler\n')
    proof=(ROOT/'lean/NativeCellAggregateReflection.lean').read_bytes()
    parts.append(no_imports(proof.decode()))
    raw=('\n'.join(parts)).encode()
    (ROOT/'lean/OnlineNativeCellAggregateReflection.lean').write_bytes(raw)
    mapping={'kind':'exact_original_source_and_ordered_compiler_projection',
        'original_sources':dict(PINS,**EXTRA_PINS),
        'already_checked_form_projection_sha256':sha(form),
        'authored_source_sha256':sha(proof),'virtual_source_sha256':sha(raw),
        'selected_sections':['complete SourceNetwork','exact original Hybrid abbreviation',
            'exact AgeAtom/Exposure/AgeConstraint declarations','exact bank variables/forms and compileCell definition',
            'exact wire decode definitions','exact ordered list compiler/toFinset and encode/decode theorems'],
        'source_graph_or_parser_admission_proved':False,
        'full_physical_import_elaboration':False,'compiler_invoked_by_preparation':False}
    (ROOT/'lean/NativeCellAggregateReflection-SOURCE-MAP.json').write_text(json.dumps(mapping,indent=2)+'\n')
    print(json.dumps({'source_only_bytes':len(raw),'virtual_sha256':sha(raw),'compiler_invoked':False}))


if __name__=='__main__':main()
