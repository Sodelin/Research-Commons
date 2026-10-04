#!/usr/bin/env python3
"""Exact source/compiler boundary tests on EXISTING admitted G4 fixtures."""
import json
from pathlib import Path
from fractions import Fraction as Q
import sympy as sp
from symbolic_core import compile_core
from source_checks import root_two_hybrids,compile_source

ROOT=Path(__file__).resolve().parent
def main():
    source=root_two_hybrids();allocation={t:1 for t in 'abcd'};h0,h1=sp.symbols('sameOriginalGammaH0 sameOriginalGammaH1')
    gamma={'H0':h0,'H1':h1};values={h0:sp.Rational(2,5),h1:sp.Rational(3,7)};cases=[]
    for mode in ('common','independent'):
        rows={}
        for name,forcing in [('natural',{}),('force0',{'H0':0}),('force1',{'H0':1})]:
            symbolic=compile_core(source,allocation,mode,forcing,gamma_parameters=gamma)
            numeric=compile_source(source,allocation,mode,forcing)
            if set(symbolic)!=set(numeric) or any(sp.cancel(symbolic[t].subs(values)-sp.Rational(p.numerator,p.denominator))!=0 for t,p in numeric.items()):raise AssertionError('Symbolic source lost actual joint covariance.')
            rows[name]=symbolic
        common_identity=all(sp.expand(rows['natural'].get(t,0)-h0*rows['force0'].get(t,0)-(1-h0)*rows['force1'].get(t,0))==0 for t in set().union(*(set(v) for v in rows.values())))
        assert common_identity==(mode=='common')
        cases.append({'mode':mode,'same_original_parameters_in_all_rows':True,'full_rooted_law_matches_pinned_joint_compiler':True,'common_endpoint_identity':common_identity})
    rejected=[]
    for slot,protected in [('ru',()),('h0a',('h0a',))]:
        try:compile_core(source,allocation,'common',slots={slot:lambda k:{}},protected_edges=protected)
        except ValueError:rejected.append(slot)
        else:raise AssertionError('Illegal/source-protected chain slot accepted.')
    out={'status':'PASS_JOINT_SYMBOLIC_ACTUAL_CORE_COMPILER_BOUNDARY','cases':cases,'illegal_and_protected_slots_rejected':rejected,
         'complete_retained_core_census_claimed':False,'general_global_NO_from_fixture_claimed':False,'new_graph_census_or_source_case_added':False}
    (ROOT/'SYMBOLIC-CORE-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
