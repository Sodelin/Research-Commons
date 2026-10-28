#!/usr/bin/env python3
"""Compose exact existing physical/wire receiver sections; no compiler runs."""
import argparse
import hashlib
import json
from pathlib import Path
from prepare_chart_form_projection import between, no_imports

ROOT=Path(__file__).resolve().parent
PINS={
 'G5CalendarRoutes':'db0e9421d59009e4119ac42e7e86517ada50f5007a314fd430f4b0937f6c80fd',
 'UnifiedLean.Source.NativePairClockLaw':'470738f7397f640a76374f791c485d757d1e2ac38769a11f05d0abc03c8aa9ae',
 'UnifiedLean.Source.NativeIndependentPairMixture':'4e1107890e0e36967898c06251a1a7ed3305721860534b902a87b04d434e4c31',
 'G6NaturalCellInverseRates':'bd35c3f3f47ada67cceb9887059a3a9ed8662129bcab4dbe5d5ade07a377de5f',
 'NaturalCellAffineCompiler':'b381a99725e1817b93a48a8356c282c08b6198d36794a2b5cd358f5368161ea0',
 'G6RationalAffineWitness':'82da8185b8ac86eb1bcadcf75ec8c5962fd082eae65a3614bf7e7c188a70f1d3',
 'G6WireAffineRefinement':'d5131590649cc79ff7337b35aa0dbca44964585c8b72c25af812b05d84b78737',
 'G6AffineContradictionCertificate':'7574ce62db7caa0ff28f46458888d1c150ce1a9bcdc6bdffa2bc43a226757b7e',
 'G6WireContradictionRefinement':'2d6efd88c767a8edaa7175c0c7351e5460e1d801290a1a59ca54fa02c898f806',
 'G6RationalNaturalCellWitness':'4d719dabb10d5d6175d95a6c8bfd43d6829a57067db85139d8b59ea27c450254',
}

def sha(raw):return hashlib.sha256(raw).hexdigest()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source-store',type=Path,required=True)
    args=p.parse_args()
    src={}
    for name,digest in PINS.items():
        raw=(args.source_store/(digest+'.lean')).read_bytes()
        if sha(raw)!=digest:raise ValueError('ORIGINAL_SOURCE_CHANGED: '+name)
        src[name]=raw.decode()
    previous=(ROOT/'lean/OnlineOriginalCodeChartReflection.lean').read_bytes()
    if sha(previous)!='d6c72ea5289bf4b7d23650bdf8f3a38ca23054555ef4b2b72e32cfceeb053712':
        raise ValueError('CHECKED_CODE_COMPONENT_CHANGED')
    parts=[previous.decode()]
    binders=('variable {V E X I C : Type*}\n'
      'variable [Fintype V] [Fintype E] [Fintype X] [Fintype I] [Fintype C]\n'
      'variable [DecidableEq V] [DecidableEq E] [DecidableEq I] [DecidableEq C]\n')
    physical_opens=('open Nanuq.Source GProgram.G5\n'
      'open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw\n'
      'open UnifiedLean.Source.NativeIndependentPairMixture\n')
    parts.append('namespace GProgram.G5\nopen Nanuq.Source\n'+
      'variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]\n'+
      between(src['G5CalendarRoutes'],'structure Calendar (G : EdgeGraph V E)','def Calendar.Active')+
      '\nend GProgram.G5\n')
    parts.append('namespace UnifiedLean.Source.NativePairClockLaw\nvariable {E : Type*}\n'+
      between(src['UnifiedLean.Source.NativePairClockLaw'],'structure PositivePairRates (E : Type*)',
        '/-- The none coordinate')+'\nend UnifiedLean.Source.NativePairClockLaw\n')
    parts.append('namespace UnifiedLean.Source.NativeIndependentPairMixture\n'
      'open Nanuq.Source UnifiedLean.Source.NativeParentRouting\n'
      'variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]\n'+
      between(src['UnifiedLean.Source.NativeIndependentPairMixture'],
        'structure HybridProbabilities (N : RootedBinary V E X)','abbrev NativeCoinSeed')+
      '\nend UnifiedLean.Source.NativeIndependentPairMixture\n')
    inv=src['G6NaturalCellInverseRates']
    parts.append('namespace UnifiedLean.G6.NaturalCellInverseRates\n'+physical_opens+binders+
      between(inv,'theorem interval_div_iff','/-- An endpoint is a literal')+
      between(inv,'theorem all_hazard_cells_iff','/-- Rational affine chronology')+
      between(inv,'def originalCellFeasible (N : RootedBinary V E X)','#print axioms interval_div_iff')+
      '\nend UnifiedLean.G6.NaturalCellInverseRates\n')
    aff=src['NaturalCellAffineCompiler']
    parts.append('namespace UnifiedLean.G6.NaturalCellAffineCompiler\n'+physical_opens+
      'open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.NaturalCellInverseRates\n'+
      binders+'variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)\n'+
      between(aff,'@[simp] theorem ageForm_eval','def chronologyRows')+
      between(aff,'@[simp] theorem chronologyRows_holds','/-- Finite syntactic compilation')+
      between(aff,'def BankConditions','/-- An actual total executable')+
      '\nend UnifiedLean.G6.NaturalCellAffineCompiler\n')
    parts.append(no_imports(src['G6RationalAffineWitness']))
    wire=src['G6WireAffineRefinement']
    parts.append('namespace UnifiedLean.G6.WireAffineRefinement\n'
      'open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.RationalAffineWitness\n'
      'open scoped BigOperators\n'+between(wire,'theorem ofFn_decodeVector','#print axioms ofFn_decodeVector')+
      '\nend UnifiedLean.G6.WireAffineRefinement\n')
    parts.extend(no_imports(src[n]) for n in ('G6AffineContradictionCertificate','G6WireContradictionRefinement'))
    nat=src['G6RationalNaturalCellWitness']
    parts.append('namespace UnifiedLean.G6.RationalNaturalCellWitness\n'+physical_opens+
      'open UnifiedLean.G6.StrictAffineElimination UnifiedLean.G6.RationalAffineWitness\n'
      'open UnifiedLean.G6.NaturalCellInverseRates UnifiedLean.G6.NaturalCellAffineCompiler\n'+binders+
      'variable (N : RootedBinary V E X) {n : ℕ} (layout : BankVar N ≃ Fin n)\n'+
      between(nat,'def checkOriginalCellWitness','theorem solveOriginalCell_sound')+
      between(nat,'structure OriginalCellBank','/-- Executable output carries')+
      between(nat,'theorem checkedOriginalCellBank_feasible','#print axioms checkOriginalCellWitness_sound')+
      '\nend UnifiedLean.G6.RationalNaturalCellWitness\n')
    owned=(ROOT/'lean/OriginalCodeChartReceiver.lean').read_bytes()
    parts.append(no_imports(owned.decode()))
    raw=('\n'.join(parts)).encode()
    (ROOT/'lean/OnlineOriginalCodeChartReceiver.lean').write_bytes(raw)
    (ROOT/'lean/OriginalCodeChartReceiver-SOURCE-MAP.json').write_text(json.dumps({
      'kind':'exact_existing_physical_and_wire_receiver_composition_projection',
      'original_sources':PINS,'previous_checked_code_projection_sha256':sha(previous),
      'authored_source_sha256':sha(owned),'virtual_bytes':len(raw),'virtual_sha256':sha(raw),
      'selected_sections':['exact Calendar/PositivePairRates/pairRate/HybridProbabilities carriers',
        'original reciprocal/feasibility and full compileCell correctness equivalences',
        'original rational checker, wire witness and contradiction semantics',
        'original direct physical-bank constructor and field theorems'],
      'byte_parser_refinement':False,'native_execution':False,'full_native_import_elaboration':False,
      'compiler_invoked_by_preparation':False},indent=2)+'\n')
    print(json.dumps({'source_only_bytes':len(raw),'virtual_sha256':sha(raw),'compiler_invoked':False}))

if __name__=='__main__':main()
