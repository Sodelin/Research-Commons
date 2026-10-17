"""Exact rational check of a lower bound on the bound, not physical impossibility."""
from fractions import Fraction as F
import json,pathlib,sys
if sys.flags.optimize: raise RuntimeError('Run without -O')
p=pathlib.Path(__file__).resolve().parent
r=json.loads((p/'RESULT.json').read_text())
rho=F(r['rho_lower']); eta=F(r['measurement_eta_e2_over_h'])
kb=F(1380649,10**29)/F(1602176634,10**31)
theta=kb/1000
assert theta>=rho
assert 16*eta*theta>rho*rho
print('PASS: for T>=1 mK, any 0<W<rho and y>=0, candidate17 bound cannot certify Q>0 with eta=0.001.')
print('Squared lower bound on inferred conductance upper bound:',float(16*eta*theta/(rho*rho)))
print('This is a limitation of this worst-case bound, not of the actual physical response.')
