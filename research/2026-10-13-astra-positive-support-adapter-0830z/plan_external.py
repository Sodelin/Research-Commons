#!/usr/bin/env python3
"""Compiler-derived import closure only; no source compilation."""
from pathlib import Path
import argparse
import json
import sys
import hashlib

HERE=Path(__file__).resolve().parent
PREVIOUS=HERE.parent/'2026-10-13-astra-unified-solver-0645z'
sys.path.insert(0,str(PREVIOUS))
import build_mathlib_serial as serial
from build_lean import verify_dependency_state

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--mathlib-root',type=Path,required=True)
p.add_argument('--lean-bin',type=Path,required=True)
p.add_argument('--previous-state',type=Path,required=True)
p.add_argument('--out',type=Path,required=True)
a=p.parse_args()
repos,pins,env=serial.setup(a.mathlib_root,a.lean_bin)
reuse=verify_dependency_state(a.previous_state,repos,a.lean_bin,pins)
previous=json.loads((a.previous_state/'PLAN.json').read_text())
selection=json.loads((HERE/'PROVIDER-SELECTION.json').read_text())
serial.ROOTS=sorted(set(selection['external']+[r['module'] for r in selection['owned'] if r['module'].startswith('Mathlib.')] + serial.ROOTS))
serial.ROOTS=[n for n in serial.ROOTS if not n.startswith(('Lean.','Init.','Std.','Lake.'))]
rows=serial.plan(a.mathlib_root,a.lean_bin,repos,env,previous['modules'])
result=dict(mathlib_pin=serial.PIN,compiler_sha256=serial.LEAN_SHA,dependencies=pins,
            roots=serial.ROOTS,modules=rows,previous_plan_sha256=reuse['plan_sha256'],
            previous_authenticated_modules=len(previous['modules']),
            additional_uncompiled_modules=len(rows)-len(previous['modules']),
            source_compilation_performed=False,
            command_contract=[str(a.lean_bin/'lean'),'-j','1','-s','8192','--src-deps','SOURCE'])
with a.out.open('x') as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps(dict(status='COMPILER_DERIVED_IMPORT_CLOSURE_ONLY',total=len(rows),
                     authenticated_reuse=len(previous['modules']),additional_uncompiled=result['additional_uncompiled_modules'],
                     plan_sha256=hashlib.sha256(a.out.read_bytes()).hexdigest())),flush=True)
