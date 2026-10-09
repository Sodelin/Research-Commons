"""G6 natural hazard-cell compiler on a supplied admitted graph/order chart.

The caller supplies original IDs and the complete weak order. Graph admission,
complete chart enumeration and downstream probability compilation are separate.
All finite exposures sharing a physical ID use one positive inverse rate.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from rational_affine_feasibility import Row, solve

@dataclass(frozen=True)
class Atom:
    node: str | None = None
    cut: Q = Q(0)

@dataclass(frozen=True)
class Bound:
    value: Q
    strict: bool = False

@dataclass(frozen=True)
class Interval:
    lower: Bound | None = None
    upper: Bound | None = None

@dataclass(frozen=True)
class Exposure:
    population: str
    younger: Atom
    older: Atom
    cell: Interval

@dataclass(frozen=True)
class Order:
    left: Atom
    right: Atom
    relation: str # <, <=, =

@dataclass(frozen=True)
class Chart:
    nodes: tuple
    populations: tuple # original edge IDs plus a distinct ancestral ID
    hybrids: tuple
    edges: tuple # (original edge ID, older node, younger node)
    tips: tuple
    orders: tuple
    exposures: tuple
    coins: tuple # (original hybrid ID, interval)


def compile_chart(chart):
    groups=[chart.nodes,chart.populations,chart.hybrids]
    if any(len(set(g))!=len(g) for g in groups):
        raise ValueError('duplicate original ID within a registry')
    keys=[('age',x) for x in chart.nodes]+[('inverse_rate',x) for x in chart.populations]+[('gamma',x) for x in chart.hybrids]
    positions={key:i for i,key in enumerate(keys)}
    n=len(keys); rows=[]
    def variable(kind,key):
        a=[Q(0)]*n;a[positions[kind,key]]=Q(1);return a,Q(0)
    def atom(x):
        return variable('age',x.node) if x.node is not None else ([Q(0)]*n,Q(x.cut))
    def sub(x,y):return ([a-b for a,b in zip(x[0],y[0])],x[1]-y[1])
    def scale(c,x):return ([Q(c)*a for a in x[0]],Q(c)*x[1])
    def le(x,y,strict=False):
        a,b=sub(x,y);rows.append(Row(tuple(a),-b,strict))
    zero=([Q(0)]*n,Q(0));one=([Q(0)]*n,Q(1))
    for e in chart.populations:le(zero,variable('inverse_rate',e),True)
    for h in chart.hybrids:
        g=variable('gamma',h);le(zero,g,True);le(g,one,True)
    for edge,older,younger in chart.edges:
        if edge not in chart.populations:raise ValueError('missing original physical rate')
        le(variable('age',younger),variable('age',older),True)
    for tip in chart.tips:
        a=variable('age',tip);le(a,zero);le(zero,a)
    for order in chart.orders:
        if order.relation not in ('<','<=','='):raise ValueError('invalid order relation')
        a,b=atom(order.left),atom(order.right);le(a,b,order.relation=='<')
        if order.relation=='=':le(b,a)
    for exposure in chart.exposures:
        d=sub(atom(exposure.older),atom(exposure.younger))
        u=variable('inverse_rate',exposure.population)
        cell=exposure.cell
        if cell.lower:le(scale(cell.lower.value,u),d,cell.lower.strict)
        if cell.upper:le(d,scale(cell.upper.value,u),cell.upper.strict)
    for hybrid,cell in chart.coins:
        g=variable('gamma',hybrid)
        if cell.lower:le(([Q(0)]*n,Q(cell.lower.value)),g,cell.lower.strict)
        if cell.upper:le(g,([Q(0)]*n,Q(cell.upper.value)),cell.upper.strict)
    return keys,rows


def solve_chart(chart,max_pairs=None):
    keys,rows=compile_chart(chart)
    witness=solve(rows,len(keys),max_pairs=max_pairs)
    if witness is None:return None
    d=dict(zip(keys,witness))
    bank={'ages':{x:d['age',x] for x in chart.nodes},
          'rates':{e:1/d['inverse_rate',e] for e in chart.populations},
          'gammas':{h:d['gamma',h] for h in chart.hybrids}}
    # Independent final check in the original multiplicative coordinates.
    def value(atom):return bank['ages'][atom.node] if atom.node is not None else Q(atom.cut)
    def inside(x,c):
        return ((c.lower is None or (x>c.lower.value if c.lower.strict else x>=c.lower.value)) and
                (c.upper is None or (x<c.upper.value if c.upper.strict else x<=c.upper.value)))
    assert all(inside(bank['rates'][e.population]*(value(e.older)-value(e.younger)),e.cell) for e in chart.exposures)
    assert all(inside(bank['gammas'][h],c) for h,c in chart.coins)
    return bank
