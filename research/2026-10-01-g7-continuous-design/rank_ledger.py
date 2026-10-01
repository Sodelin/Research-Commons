"""Exact rational affine-measurement deletion certificates.

An oracle returns an EXACT vector B*z+b for one fixed unknown z. This is not
a finite-sample/noisy measurement model. The hand theorem also allows real
coefficients; this executable ledger uses exact rational arithmetic only.
"""
from fractions import Fraction as F


def rational(x):
    if isinstance(x, float):
        raise TypeError('Floating input is not an exact rational contract.')
    return F(x)


class ExactLedger:
    def __init__(self, dimension):
        if not isinstance(dimension,int) or dimension<0:
            raise ValueError('Dimension must be a nonnegative integer.')
        self.dimension=dimension
        self.basis=[]
        self.oracle_calls=0
        self.simulated_calls=0

    def _reduce(self,row):
        r=list(row); known=F(0)
        for pivot,base,value in self.basis:
            a=r[pivot]
            if a:
                r=[x-a*y for x,y in zip(r,base)]
                known+=a*value
        return r,known

    def query(self,matrix,offset,oracle):
        rows=[tuple(map(rational,row)) for row in matrix]
        offset=tuple(map(rational,offset))
        if len(rows)!=len(offset) or any(len(row)!=self.dimension for row in rows):
            raise ValueError('Measurement dimensions disagree.')
        reduced=[self._reduce(row) for row in rows]
        if all(not any(r) for r,_ in reduced):
            self.simulated_calls+=1
            return tuple(v+b for (_,v),b in zip(reduced,offset))
        values=tuple(map(rational,oracle(rows,offset)))
        if len(values)!=len(rows):
            raise ValueError('Oracle returned the wrong number of coordinates.')
        self.oracle_calls+=1
        before=len(self.basis)
        for row,value,b in zip(rows,values,offset):
            residual,known=self._reduce(row)
            if not any(residual):
                if value-b!=known:
                    raise ValueError('Oracle violates the fixed exact-law contract.')
                continue
            pivot=next(i for i,x in enumerate(residual) if x)
            scale=residual[pivot]
            self.basis.append((pivot,tuple(x/scale for x in residual),(value-b-known)/scale))
            self.basis.sort(key=lambda x:x[0])
        assert before<len(self.basis)<=self.dimension
        return values

    @property
    def rank(self):
        return len(self.basis)
