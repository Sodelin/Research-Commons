"""Supplemental fixture-schema guard for the earlier G5 self-audit.

The old verifier's declared inheritance keys must equal the structural hybrids.
This guard is not an arbitrary genealogy-law source-recognition algorithm.
"""
from collections import Counter
from fractions import Fraction


def validate_source_record(record):
    ages = record['ages'] if 'ages' in record else record['ages_in_units_of_log_2']
    labels = tuple(record['labels'])
    if len(labels) != len(set(labels)) or not set(labels) <= set(ages):
        raise ValueError('Invalid sampled taxon labels')
    incoming = Counter(e['child'] for e in record['edges'])
    outgoing = Counter(e['parent'] for e in record['edges'])
    actual = {v for v in ages if incoming[v] == 2}
    if set(record['inheritance']) != actual:
        raise ValueError('Inheritance keys must equal the structural hybrid vertices')
    if any(not 0 < Fraction(g) < 1 for g in record['inheritance'].values()):
        raise ValueError('Inheritance must be strictly interior')
    if {v for v in ages if outgoing[v] == 0} != set(labels):
        raise ValueError('Sampled taxa must be exactly the leaf vertices')
    if any(e['parent'] not in ages or e['child'] not in ages for e in record['edges']):
        raise ValueError('Edge endpoint has no age')
    if len({e['id'] for e in record['edges']}) != len(record['edges']):
        raise ValueError('Duplicate edge identifiers')
    return True
