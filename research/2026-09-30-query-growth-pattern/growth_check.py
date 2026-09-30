"""Exact arithmetic checks for the classical tree-count query obstruction."""
import json
from math import factorial, prod, comb
from fractions import Fraction


def tree_count(n):
    return prod(range(1, 2*n-4, 2))


def ternary_lower(count):
    power, q = 1, 0
    while power < count:
        power *= 3
        q += 1
    return q


def check():
    entries = []
    first = None
    previous = 1
    for n in range(4, 101):
        count = tree_count(n)
        m = n-2
        assert count == factorial(2*m)//(2**m*factorial(m))
        assert count == previous*(2*n-5)
        previous = count
        q = ternary_lower(count)
        assert 3**(q-1) < count <= 3**q
        candidate = 3*n-10
        if n >= 5 and first is None and count > 3**candidate:
            first = n
        if n in (4,5,6,7,8,9,10,11,12,34):
            entries.append({'n':n,'tree_count':count,'tree_query_lower_bound':q,
                            'candidate_3n_minus_10':candidate})
    assert first == 34
    assert 3**92 < tree_count(34) <= 3**93
    ratio = Fraction(6955830,145845)
    return {'status':'PASS','tree_formulas_checked_through_n':100,
            'first_counting_contradiction_for_n_ge_5':first,
            'integer_comparison_at_34':{'three_to_92':3**92,
                                      'trees':tree_count(34),'three_to_93':3**93},
            'selected_bounds':entries,
            'owner_reported_profile_ratio_8_to_7':{'exact':str(ratio),'decimal':float(ratio)},
            'quartet_query_counts':{'7':comb(7,4),'8':comb(8,4)},
            'not_run':['catalogue','minimax','large certificate replay','runtime benchmark','Lean']}


if __name__ == '__main__':
    print(json.dumps(check(),indent=2))
