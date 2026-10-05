"""Typed CAD principal-root values to history-only isolated policy sections.

Supported roots are positive principal p/q powers whose radicand lies strictly
between zero and one on the selected history cell. Existence and uniqueness
are NOT asserted by this serializer: the mandatory all-source policy gate
proves them. General multiplicity-indexed Root and root-bearing guards remain
UNKNOWN until an exact index/isolation bridge is implemented.
"""
import json,re
import z3
from cad_value import evaluate_value

class SectionEncodingLimit(ValueError):
    pass

class ActionSectionWriter:
    def __init__(self, step, max_nodes=4096, max_degree=128):
        if type(step) is not int or step < 0:
            raise ValueError('Invalid original policy call index.')
        self.step=step;self.sections=[];self.cache={};self.nodes=0
        self.max_nodes=max_nodes;self.max_degree=max_degree
    def text(self,node,depth=0):
        self.nodes+=1
        if self.nodes>self.max_nodes or depth>64:
            raise SectionEncodingLimit('Exact CAD action AST exceeds resource ceiling.')
        if not isinstance(node,dict):raise ValueError('Malformed exact CAD action value.')
        kind=node.get('kind')
        child=lambda value:self.text(value,depth+1)
        if kind=='rational' and set(node)=={'kind','value'}:
            record,value=evaluate_value(node,{})
            if record['status']!='EXACT_STRUCTURED_CAD_VALUE_SAME_BACKEND' or not z3.is_rational_value(value):
                raise ValueError('Malformed exact rational action constant.')
            return str(value.as_fraction())
        if kind=='observation' and set(node)=={'kind','name'}:
            name=node['name']
            if not isinstance(name,str) or not re.fullmatch(r'h[0-9]+_[0-9]+',name):
                raise ValueError('CAD action may read only typed recorded observations.')
            return name
        if kind in ('add','multiply') and set(node)=={'kind','args'} and isinstance(node['args'],list) and node['args']:
            return '('+('+' if kind=='add' else '*').join(child(v) for v in node['args'])+')'
        if kind=='divide' and set(node)=={'kind','numerator','denominator'}:
            return '('+child(node['numerator'])+')/('+child(node['denominator'])+')'
        if kind=='power' and set(node)=={'kind','base','exponent'} and type(node['exponent']) is int:
            if abs(node['exponent'])>self.max_degree:raise SectionEncodingLimit('Written action exponent exceeds resource ceiling.')
            base=child(node['base']);exponent=node['exponent']
            return ('1/(('+base+')**'+str(-exponent)+')' if exponent<0 else '('+base+')**'+str(exponent))
        if (kind=='principal_power' and set(node)=={'kind','base','numerator','denominator'}
                and type(node['numerator']) is int and type(node['denominator']) is int):
            p,q=node['numerator'],node['denominator']
            if not 2<=q<=self.max_degree or abs(p)>self.max_degree:
                raise SectionEncodingLimit('Unsupported principal-root exponent/resource carrier.')
            key=json.dumps(node,sort_keys=True,separators=(',',':'))
            if key in self.cache:return self.cache[key]
            base=child(node['base'])
            name=f'action_root_cad_step{self.step}_section{len(self.sections)}'
            self.sections.append({'name':name,'coefficients':['-('+base+')']+['0']*(q-1)+['1'],
                                  'lower':'0','upper':'1'})
            value=('1/(('+name+')**'+str(-p)+')' if p<0 else '('+name+')**'+str(p))
            self.cache[key]=value
            return value
        raise ValueError('Unsupported general indexed Root/min/max CAD action shape.')
    def call(self,weights,support):
        if not isinstance(weights,list) or not weights:raise ValueError('Empty CAD action carrier.')
        texts=[self.text(node) for node in weights]
        return {'support':support,'weights':texts,**({'sections':self.sections} if self.sections else {})}
