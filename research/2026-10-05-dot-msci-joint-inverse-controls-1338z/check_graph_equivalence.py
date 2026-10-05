"""Bounded exact symbolic substitution check; no source-point or contractor trial."""
import hashlib,json
from pathlib import Path
from fractions import Fraction as F
import sympy as sp
import interval_ad as ad
import interval_math as m

def verify():
    x={key:sp.Symbol(key,positive=True) for key in ad.COORDS};p={key:x[key] for key in ('h','rA','rB','rC','rAB','rR','g')};p['t1']=x['h']+x['u'];p['t0']=p['t1']+x['v'];checks=[]
    for k in (1,2):
        z=F(8*k,3);original=m.forward.pair_expressions(p,z,lambda a:sp.exp(-a));rewritten=ad.physical_pair_expressions(x,z,lambda a:sp.exp(-a))
        for pair in m.forward.PAIRS:
            difference=sp.expand(original[pair]-rewritten[pair])
            if difference!=0:raise AssertionError('value graph differs: '+pair)
            for key in ad.COORDS:
                if sp.diff(original[pair],x[key])-sp.diff(rewritten[pair],x[key])!=0:raise AssertionError('physical derivative graph differs')
            checks.append({'pair':pair,'k':k,'exact_value_difference':'0','all_nine_physical_derivative_differences':'0'})
    return {'schema':'exact-physical-graph-substitution-v1','sympy_version':sp.__version__,'provider_sha256':m.SOURCE_SHA,'rewritten_source_sha256':hashlib.sha256(Path(ad.__file__).read_bytes()).hexdigest(),'checks':checks,'exact_value_identities':12,'exact_derivative_identities':108,'new_source_points_evaluated':0,'contractor_controls_run':0}
if __name__=='__main__':print(json.dumps(verify(),sort_keys=True,indent=2))
