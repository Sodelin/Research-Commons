"""Exact complete-genealogy KL upper bound, valid for every locus length."""
from fractions import Fraction as F
from pathlib import Path
import json
import certify_unknown_calendar_inverse as ci
# log(11/10), alternating odd truncation upper bound.
log_upper=sum((-1)**(n+1)*F(1,10)**n/n for n in range(1,42))
kl_upper=ci.expneg(ci.I(1)).hi*(log_upper-F(1,11))
necessary_loci=(F(81,50)/kl_upper).__ceil__()
x={'status':'passed exact scalar bound','sources':[['1','2','1'],['1','11/5','1']],'target_eta':'1/10','KL_P1_P0_upper':str(kl_upper),'necessary_loci_every_length':necessary_loci,'necessary_calls_formula':f'2*L*{necessary_loci}','fixed_call_budget':60000000,'largest_length_not_ruled_out_by_this_bound':60000000//(2*necessary_loci),'scope':'Necessary two-point 95% accuracy at both sources for any observation channel of one genealogy per locus; not sufficiency or optimum.'}
Path(__file__).with_name('long-locus-obstruction-control.json').write_text(json.dumps(x,indent=2)+'\n')
print({k:x[k] for k in ['necessary_loci_every_length','largest_length_not_ruled_out_by_this_bound']})
