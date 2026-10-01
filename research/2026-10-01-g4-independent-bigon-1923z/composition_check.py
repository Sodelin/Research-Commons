#!/usr/bin/env python3
"""Exact source-admitted obstruction to commuting a Kingman edge and bigon."""
from __future__ import annotations
from fractions import Fraction as Q
from hashlib import sha256
from pathlib import Path
import json
import verify


def run() -> dict:
    theta = (Q(1,2), Q(3,4), Q(1,3))
    z = Q(2,3)
    pad = Q(1,2)
    commutators = {}
    for k in range(1, 7):
        values = []
        for r in range(1, k+1):
            eb = sum((verify.p(k,j,z)*verify.b(j,r,*theta)
                      for j in range(r,k+1)), Q(0))
            be = sum((verify.b(k,j,*theta)*verify.p(j,r,z)
                      for j in range(r,k+1)), Q(0))
            values.append(eb-be)
        if k <= 3:
            assert all(v == 0 for v in values)
        if k == 4:
            assert values == [Q(-211,393660),Q(211,393660),Q(0),Q(0)]
        commutators[str(k)] = [str(v) for v in values]
    left = verify.response(4,pad*z,pad,theta)
    right = verify.response(4,pad,z*pad,theta)
    difference = left-right
    assert difference == Q(-211,75582720)
    for k in range(1,4):
        assert verify.response(k,pad*z,pad,theta) == verify.response(k,pad,z*pad,theta)
    here = Path(__file__)
    return {
        'status':'PASS',
        'arithmetic':'exact fractions.Fraction',
        'source_sha256':sha256(here.read_bytes()).hexdigest(),
        'verify_dependency_sha256':sha256((here.parent/'verify.py').read_bytes()).hexdigest(),
        'bigon_parameters':[str(v) for v in theta],
        'left_leading_trailing_survivals':['1/3','1/2'],
        'right_leading_trailing_survivals':['1/2','1/3'],
        'unpadded_count_commutators':commutators,
        'observed_A_clade':{'A_copies':4,'total_four_taxon_copies':7,
                            'left':str(left),'right':str(right),'difference':str(difference)},
        'limits':['All-labelled-forest equality through three input roots follows from the hand proof using exchangeability; the code checks count laws.',
                  'This is an exact ordering obstruction, not an undecidability theorem.',
                  'No positive edge has zero duration; all physical survivals are interior.']
    }


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
