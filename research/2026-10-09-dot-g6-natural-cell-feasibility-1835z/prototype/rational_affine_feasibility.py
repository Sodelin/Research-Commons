"""Classical strict Fourier--Motzkin with exact witness back-substitution.

Rows are a*x <= b (strict=True means <). This general rational interface
allows unbounded inverse rates. It is not a graph/cell admission checker.
No budget by default: termination is mathematical, not a practicality claim.
"""
from dataclasses import dataclass
from fractions import Fraction as Q

@dataclass(frozen=True)
class Row:
    a: tuple
    b: Q
    strict: bool = False

    def __post_init__(self):
        if type(self.strict) is not bool:
            raise TypeError('literal strictness Boolean required')
        object.__setattr__(self, 'a', tuple(Q(x) for x in self.a))
        object.__setattr__(self, 'b', Q(self.b))

    def holds(self, x):
        v = sum((a*y for a,y in zip(self.a,x)), Q(0))
        return v < self.b if self.strict else v <= self.b

class ResourceLimit(RuntimeError):
    """A caller ceiling was reached: UNKNOWN, never infeasible."""

def solve(rows, dimension, max_pairs=None):
    """Return an exact rational witness, or None for infeasibility.

    Every reconstructed witness is checked against every original row.
    ResourceLimit and malformed inputs must not be interpreted as NO.
    """
    if type(dimension) is not int or dimension < 0:
        raise ValueError('nonnegative integer dimension required')
    rows = list(rows)
    if any(len(r.a) != dimension for r in rows):
        raise ValueError('one shared variable bank required')
    if max_pairs is not None and (type(max_pairs) is not int or max_pairs < 0):
        raise ValueError('nonnegative integer resource ceiling required')
    original = rows[:]
    history = []
    pairs = 0
    for n in range(dimension, 0, -1):
        pos = [r for r in rows if r.a[-1] > 0]
        neg = [r for r in rows if r.a[-1] < 0]
        zero = [Row(r.a[:-1],r.b,r.strict) for r in rows if r.a[-1] == 0]
        history.append((pos,neg))
        pairs += len(pos)*len(neg)
        if max_pairs is not None and pairs > max_pairs:
            raise ResourceLimit('Fourier--Motzkin pair ceiling reached')
        for p in pos:
            for m in neg:
                # Add positive multiples of the two inequalities, cancelling
                # the last coordinate. Strictness is logical OR.
                cp,cm = -m.a[-1],p.a[-1]
                zero.append(Row(tuple(cp*x+cm*y for x,y in zip(p.a[:-1],m.a[:-1])),
                                cp*p.b+cm*m.b,p.strict or m.strict))
        rows = list(dict.fromkeys(zero))
    if any(not r.holds(()) for r in rows):
        return None
    x=[]
    for pos,neg in reversed(history):
        def endpoint(r):
            return (r.b-sum((a*y for a,y in zip(r.a[:-1],x)),Q(0)))/r.a[-1]
        lower=max((endpoint(r) for r in neg),default=None)
        upper=min((endpoint(r) for r in pos),default=None)
        if lower is None:
            z=Q(0) if upper is None else upper-1
        elif upper is None:
            z=lower+1
        elif lower < upper:
            z=(lower+upper)/2
        else:
            assert lower == upper
            assert all(not r.strict for r in neg if endpoint(r)==lower)
            assert all(not r.strict for r in pos if endpoint(r)==upper)
            z=lower
        x.append(z)
    assert all(r.holds(x) for r in original)
    return tuple(x)
