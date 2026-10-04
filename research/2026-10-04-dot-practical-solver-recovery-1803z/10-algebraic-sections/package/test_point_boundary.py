#!/usr/bin/env python3
"""Malformed/resource-limited point encodings must return explicit UNKNOWN."""
import json
from pathlib import Path
import z3
from section_point import evaluate_section

def main():
    cases=[]
    for name,coefficients in [('syntax',['(','0','1']),('depth',['+'.join(['1']*1100),'0','1']),
                              ('hidden_symbol',['-unobserved_source','0','1']),('undefined_division',['1/0','0','1'])]:
        section={'coefficients':coefficients,'lower':'0','upper':'1'}
        out,value=evaluate_section(section,{})
        assert out['status']=='UNKNOWN_UNSUPPORTED_SECTION_POINT' and value is None,(name,out)
        cases.append({'case':name,'result':out})
    good,value=evaluate_section({'coefficients':['-h0_0','0','1'],'lower':'0','upper':'1'},{'h0_0':z3.RealVal('2/3')})
    assert good['status']=='EXACT_ISOLATED_SECTION_POINT' and value is not None
    p=Path(__file__).resolve().parent;(p/'POINT-BOUNDARY-CONTROLS.json').write_text(json.dumps({'status':'PASS_POINT_BOUNDARY_UNKNOWN','cases':cases,'valid_point':good},indent=2)+'\n')
    print(json.dumps({'status':'PASS_POINT_BOUNDARY_UNKNOWN','controls':len(cases)},indent=2))

if __name__=='__main__':main()
