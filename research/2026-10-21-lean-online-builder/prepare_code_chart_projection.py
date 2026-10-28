#!/usr/bin/env python3
"""Prepare exact finite-code/decoder projections, reusing the checked aggregate."""
import argparse
import hashlib
import json
from pathlib import Path
from prepare_chart_form_projection import between, no_imports

ROOT=Path(__file__).resolve().parent
PINS={
 'G2LiveLineageRouting':'bf33f6be93e61960aa637df34d1197316669d6f2ddde6d743ac405a010cb05af',
 'UnifiedLean.Source.NativeParentRouting':'300d7216193e945ca26161535c1bc2ba75a128fe5c075b6a3567bbda66bfe0b6',
 'G7OriginalFiniteEncoding':'30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078',
 'G7OriginalAdmission':'16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c',
}


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-store',type=Path,required=True)
    args=parser.parse_args()
    original={}
    for name,digest in PINS.items():
        raw=(args.source_store/(digest+'.lean')).read_bytes()
        if sha(raw)!=digest:raise ValueError('ORIGINAL_SOURCE_CHANGED')
        original[name]=raw.decode()
    aggregate=(ROOT/'lean/OnlineNativeCellAggregateReflection.lean').read_bytes()
    if sha(aggregate)!='21c2e9a0bc27610b0494d6e40a5ba295a8a62997e7f7e6f117466e39deda53e7':
        raise ValueError('CHECKED_AGGREGATE_CHANGED')
    parts=['import Mathlib.Data.Fintype.Inv\nimport Mathlib.Logic.Equiv.Fin.Basic\n',aggregate.decode()]
    parents=original['G2LiveLineageRouting']
    parts.append('namespace GProgram.G2\nopen Nanuq.Source\n'
        'variable {V E X : Type*}\nvariable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]\n'+
        between(parents,'structure OriginalHybridParents (N : RootedBinary V E X)',
            'theorem OriginalHybridParents.parent_injective')+
        '\nend GProgram.G2\n')
    native=original['UnifiedLean.Source.NativeParentRouting']
    parts.append('namespace UnifiedLean.Source.NativeParentRouting\nopen Nanuq.Source\n'
        'variable {V E X : Type*}\nvariable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]\n'+
        between(native,'structure OriginalParentRegistry (N : RootedBinary V E X)',
            'noncomputable def canonicalParentRegistry')+
        '\nend UnifiedLean.Source.NativeParentRouting\n')
    finite=original['G7OriginalFiniteEncoding']
    parts.append('namespace GProgram.G7.OriginalFiniteEncoding\n'
        'variable {X ID : Type*} [Fintype X] [Fintype ID]\n'+
        between(finite,'def vertexCount (n r : ℕ)','theorem hybrid_card')+
        between(finite,'abbrev Code (X ID : Type*)','def allCodes')+
        '\nend GProgram.G7.OriginalFiniteEncoding\n')
    admission=original['G7OriginalAdmission']
    parts.append('namespace GProgram.G7.OriginalAdmission\nopen Nanuq.Source\n'
        'open GProgram.G7.OriginalFiniteEncoding UnifiedLean.Source.NativeParentRouting\n'
        'variable {X ID : Type*} [Fintype X] [Fintype ID] [DecidableEq X] [DecidableEq ID]\n'+
        between(admission,'abbrev NV := Fin','instance decidableBinaryValid')+
        between(admission,'def sourceOfValid (c : Code X ID)','def binaryCutChildCodes')+
        between(admission,'def codeSite (c : Code X ID)','instance decidableRegistryValid')+
        between(admission,'def decodedHybridMap (c : Code X ID)','#print axioms decidableBinaryValid')+
        '\nend GProgram.G7.OriginalAdmission\n')
    owned=[]
    for name in ('NativeOrderedBankLayout','OriginalCodeBankLayout','OriginalCodeChartReflection'):
        raw=(ROOT/'lean'/(name+'.lean')).read_bytes()
        parts.append(no_imports(raw.decode()))
        owned.append({'module':name,'bytes':len(raw),'sha256':sha(raw)})
    raw=('\n'.join(parts)).encode()
    (ROOT/'lean/OnlineOriginalCodeChartReflection.lean').write_bytes(raw)
    (ROOT/'lean/OriginalCodeChartReflection-SOURCE-MAP.json').write_text(json.dumps({
        'kind':'exact_original_code_and_decoder_definition_projection',
        'original_sources':PINS,'previous_checked_aggregate_sha256':sha(aggregate),
        'owned_sources':owned,'virtual_bytes':len(raw),'virtual_sha256':sha(raw),
        'selected_original_sections':['original parent structure/bit function and registry structure',
            'exact census counts/Code type','exact graph/root/leaf/BinaryValid/sourceOfValid declarations',
            'exact site/parent/RegistryValid and full decoded original registry/parent proofs'],
        'full_native_import_elaboration':False,'byte_parser_refinement':False,
        'compiler_invoked_by_preparation':False},indent=2)+'\n')
    print(json.dumps({'source_only_bytes':len(raw),'virtual_sha256':sha(raw),'compiler_invoked':False}))


if __name__=='__main__':main()
