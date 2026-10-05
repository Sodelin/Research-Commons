"""One predeclared ideal-source forward evaluation; never reads observed counts."""
import json
from fractions import Fraction as F
from pathlib import Path
import integration_core as c
TRUTH={'h':'1/16','u':'1/16','v':'1/16','rA':'1','rB':'2','rC':'4','rAB':'1','rR':'2','g':'1/4'}
BITS=128

def evaluate():
    source=c.read(c.BASE/'GENERATION-RECEIPT.json',c.GENERATION_RECEIPT_SHA)
    if source['physical_truth']!=TRUTH:raise ValueError('predeclared truth changed')
    x={key:F(value) for key,value in TRUTH.items()};parameters={key:str(value) for key,value in x.items() if key not in ('u','v')};parameters.update(t1=str(x['h']+x['u']),t0=str(x['h']+x['u']+x['v']))
    result=c.load_provider().m.forward.evaluate(parameters,BITS)
    return {'schema':'one-model-check-ideal-truth-v1','generation_receipt_sha256':c.GENERATION_RECEIPT_SHA,'physical_truth':TRUTH,'bits':BITS,'forward':result,'observed_data_read':False,'finite_generator_law_certified':False}
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();result=evaluate()
    with Path(a.output).open('xb') as f:f.write(c.canonical(result))
    print(c.sha(c.canonical(result)))
