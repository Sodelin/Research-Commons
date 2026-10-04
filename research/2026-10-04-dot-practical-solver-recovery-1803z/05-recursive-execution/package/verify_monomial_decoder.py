#!/usr/bin/env python3
"""Pure rational check of a delivered source-CF strict-order certificate.

No SymPy/Z3 expression evaluation. Actual catalogue/source compilation must be
rechecked separately; this verifies their delivered polynomial decoder binding.
"""
import argparse
import ast
from fractions import Fraction
import json
from pathlib import Path


def polynomial(text, names):
    zero=(0,)*len(names)
    def clean(p):return {m:c for m,c in p.items() if c}
    def add(a,b):
        out=dict(a)
        for m,c in b.items():out[m]=out.get(m,Fraction(0))+c
        return clean(out)
    def scale(a,c):return clean({m:v*c for m,v in a.items()})
    def multiply(a,b):
        out={}
        for m,c in a.items():
            for n,d in b.items():
                p=tuple(x+y for x,y in zip(m,n));out[p]=out.get(p,Fraction(0))+c*d
        return clean(out)
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value)is int:return clean({zero:Fraction(n.value)})
        if isinstance(n,ast.Name) and n.id in names:
            m=list(zero);m[names.index(n.id)]=1;return {tuple(m):Fraction(1)}
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return scale(go(n.operand),-1)
        if isinstance(n,ast.BinOp):
            a,b=go(n.left),go(n.right)
            if isinstance(n.op,ast.Add):return add(a,b)
            if isinstance(n.op,ast.Sub):return add(a,scale(b,-1))
            if isinstance(n.op,ast.Mult):return multiply(a,b)
            if isinstance(n.op,ast.Div) and set(b)=={zero}:return scale(a,1/b[zero])
            if isinstance(n.op,ast.Pow) and set(b)<= {zero}:
                power=b.get(zero,Fraction(0))
                if power.denominator!=1 or power<0:raise ValueError('Invalid monomial power')
                out={zero:Fraction(1)}
                for _ in range(power.numerator):out=multiply(out,a)
                return out
        raise ValueError('Unencoded rational polynomial')
    return go(ast.parse(text,mode='eval').body)


def verify(result_path, provider_path):
    result=json.loads(Path(result_path).read_text());provider=json.loads(Path(provider_path).read_text())
    selector=result['selector_search']['selector_certificate']
    cert=selector['structural_decoder_certificate']; records=cert['all_actual_source_polynomial_bindings']
    models=provider['models']
    if len(records)!=len(models):raise ValueError('Incomplete actual-source decoder coverage')
    action=selector['path'][0]
    if action['weights_smt2']!=['1.0'] and action['weights_smt2']!=['1']:
        raise ValueError('This independent control binds the single passive row')
    mapping={}
    for i,(record,model)in enumerate(zip(records,models)):
        if record['source_model']!=i or record['actual_target']!=model['target_code']:
            raise ValueError('Source or target binding changed')
        names=list(model['variable_mapping'].values());zero=(0,)*len(names)
        exponents=tuple(record['original_parameter_exponents'][n]for n in names)
        if not any(exponents)or any(type(p)is not int or p<0 for p in exponents):
            raise ValueError('Strict nonempty unit monomial missing')
        monomial={exponents:Fraction(1)}
        if polynomial(record['survival_monomial'],names)!=monomial:raise ValueError('Survival monomial changed')
        own=record['dominant_response_coordinate']
        if type(own)is not int or own not in range(3):raise ValueError('Invalid response coordinate')
        if own in mapping and mapping[own]!=model['target_code']:raise ValueError('Conflicting target guard')
        mapping[own]=model['target_code']
        for c,expression in enumerate(model['laws'][0]):
            expected={zero:Fraction(1),exponents:Fraction(-2,3)}if c==own else {exponents:Fraction(1,3)}
            if polynomial(expression,names)!=expected:raise ValueError('Actual source CF identity failed')
    return {'status':'PASS_PURE_RATIONAL_SOURCE_CF_MONOMIAL_IDENTITIES','source_models_checked':len(models),
            'strict_order':'A nonempty unit monomial over (0,1) is strictly below one; own minus other is 1-survival',
            'backend_trusted':False,'actual_source_catalogue_replay':'Separate required source-compiler verification'}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('result');p.add_argument('provider');a=p.parse_args()
    print(json.dumps(verify(a.result,a.provider),indent=2))
