"""Exact supplied COMMON certificate arithmetic, not source existence.

Exponents are k choose 2 for k=1,...,L, as in the selected1613 providers.
Nonnegativity is checked by an exact polynomial identity against a supplied
sum of rational weighted squares times 1, x, 1-x or x(1-x). This supported
certificate language is sufficient, not complete for all real certificates.
"""
from fractions import Fraction
import hashlib
import json
import re

MAX_BYTES = 262144
MAX_LEVEL = 8
MAX_TERMS = 16
MAX_SQUARE = 15
MAX_BITS = 128
MAX_JSON_DEPTH = 64
GRAMMAR = re.compile(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?\Z', re.ASCII)
ID = re.compile(r'[A-Za-z][A-Za-z0-9_.:-]{0,63}\Z', re.ASCII)


class Refused(ValueError):
    pass


def require(ok, reason):
    if not ok:
        raise Refused(reason)


def fields(obj, names):
    require(type(obj) is dict and set(obj) == set(names), 'missing or unsupported fields')


def rational(s):
    require(type(s) is str and len(s) <= 80 and GRAMMAR.fullmatch(s),
            'exact canonical integer or p/q token required')
    q = Fraction(s)
    require(max(abs(q.numerator).bit_length(), q.denominator.bit_length()) <= MAX_BITS,
            'rational input exceeds 128-bit cap')
    return q


def digest(obj):
    return hashlib.sha256(json.dumps(obj, sort_keys=True, separators=(',', ':'),
                                     ensure_ascii=True).encode()).hexdigest()


def pairs(items):
    result = {}
    for key, val in items:
        require(key not in result, 'duplicate JSON field: '+key)
        result[key] = val
    return result


def loads(raw):
    require(type(raw) in (bytes, str), 'JSON request must be bytes or text')
    try:
        size = len(raw) if type(raw) is bytes else len(raw.encode('utf-8'))
    except UnicodeError as error:
        raise Refused('malformed JSON encoding') from error
    require(size <= MAX_BYTES, 'request exceeds 256 KiB')
    try:
        value = json.loads(raw, object_pairs_hook=pairs,
                           parse_float=lambda _: (_ for _ in ()).throw(Refused('floating input refused')),
                           parse_constant=lambda _: (_ for _ in ()).throw(Refused('nonfinite input refused')))
        # The host Python may raise its recursion limit. Bound the accepted
        # transport independently so subsequent schema/hash operations cannot
        # inherit arbitrary-depth structures from a small JSON request.
        pending = [(value, 0)]
        while pending:
            item, depth = pending.pop()
            require(depth <= MAX_JSON_DEPTH, 'JSON nesting exceeds 64 levels')
            children = item.values() if type(item) is dict else item if type(item) is list else ()
            pending.extend((child, depth+1) for child in children)
        return value
    except Refused:
        raise
    except (RecursionError, UnicodeError, ValueError) as error:
        raise Refused('malformed JSON') from error


def add(a, b):
    out = [Fraction(0)] * max(len(a), len(b))
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] += v
    return out


def multiply(a, b):
    out = [Fraction(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def checked(certificate):
    fields(certificate, ['schema', 'level', 'coefficients', 'moments', 'nonnegative_terms'])
    require(certificate['schema'] == 'common_sparse_certificate_v1', 'unsupported certificate schema')
    level = certificate['level']
    require(type(level) is int and 1 <= level <= MAX_LEVEL, 'level outside 1..8')
    coeff, moments = [], []
    for name, out in [('coefficients', coeff), ('moments', moments)]:
        values = certificate[name]
        require(type(values) is list and len(values) == level, name+' length differs from level')
        out.extend(map(rational, values))
    require(any(coeff), 'zero sparse polynomial')
    require(moments[0] == 1 and all(0 <= y <= 1 for y in moments), 'invalid normalized moments')
    polynomial = [Fraction(0)]*(level*(level-1)//2+1)
    for k, coefficient in enumerate(coeff, start=1):
        polynomial[k*(k-1)//2] += coefficient
    terms = certificate['nonnegative_terms']
    require(type(terms) is list and 1 <= len(terms) <= MAX_TERMS, 'supply 1..16 square terms')
    reconstructed = []
    for term in terms:
        fields(term, ['weight', 'left', 'right', 'square'])
        w = rational(term['weight'])
        require(w >= 0, 'negative square weight')
        require(all(type(term[k]) is int and term[k] in (0, 1) for k in ['left', 'right']),
                'endpoint multipliers must be 0 or 1')
        sq = term['square']
        require(type(sq) is list and 1 <= len(sq) <= MAX_SQUARE, 'square polynomial outside degree cap')
        q = list(map(rational, sq))
        part = [w*t for t in multiply(q, q)]
        if term['left']:
            part = [Fraction(0)]+part
        if term['right']:
            part = multiply(part, [Fraction(1), Fraction(-1)])
        reconstructed = add(reconstructed, part)
    require(trim(polynomial) == trim(reconstructed), 'nonnegative identity mismatch')
    annihilation = sum(c*y for c, y in zip(coeff, moments))
    require(annihilation == 0, 'certificate does not exactly annihilate moments')
    return dict(status='CHECKED_RATIONAL_CERTIFICATE', certificate_sha256=digest(certificate),
                level=level, positive_support_cardinality_at_most=level-1,
                annihilation='0', nonnegative_domain='[0,1]', survival_domain='(0,1]',
                check='exact_rational_weighted_square_identity',
                native_refinement_proved=False, source_existence_certified=False)


def generate_singleton(moments):
    """Bounded acquisition from supplied data only; failure means UNKNOWN.

For y=(1,a,a^3), use x^3-3a^2*x+2a^3=(x-a)^2*(x+2a).
No latent target, extra queried moment, numerical optimizer or root guess.
"""
    require(type(moments) is list and len(moments) == 3, 'generator requires exactly levels 1,2,3')
    one, a, cube = map(rational, moments)
    if one != 1 or not 0 < a <= 1 or cube != a**3:
        return dict(status='UNKNOWN', reason='supplied moments do not fit the singleton generator')
    c = dict(schema='common_sparse_certificate_v1', level=3,
             coefficients=list(map(str, [2*a**3, -3*a*a, Fraction(1)])), moments=moments,
             nonnegative_terms=[dict(weight=str(2*a), left=0, right=0, square=[str(-a), '1']),
                                dict(weight='1', left=1, right=0, square=[str(-a), '1'])])
    # Generated coefficients can exceed the accepted transport cap. That is
    # bounded acquisition exhaustion, never an invalid-source conclusion.
    try:
        result = checked(c)
    except Refused:
        return dict(status='UNKNOWN', reason='generated certificate exceeds supported exact language')
    return dict(status='GENERATED_AND_CHECKED', certificate=c, check=result)


def identifiers(values, name):
    require(type(values) is list and len(values) <= 64 and
            all(type(x) is str and ID.fullmatch(x) for x in values) and
            len(set(values)) == len(values), 'invalid/duplicate '+name)
    return values


def common_packet(request):
    """Fixed external joint configuration, protected IDs and full pair menu.

Accepts normalized moment data, not a claim to have extracted those moments
from arbitrary input rows. No constraints on unencoded protected coordinates
are silently discarded: this version supports an empty constraint list only.
"""
    fields(request, ['schema', 'taxa', 'protected_edges', 'protected_hybrids',
                     'parameter_constraints', 'configurations', 'pairs'])
    require(request['schema'] == 'supplied_common_menu_v1', 'unsupported menu schema')
    taxa = identifiers(request['taxa'], 'taxon labels')
    require(4 <= len(taxa) <= 8, 'conditional theorem/menu implementation requires 4..8 taxa')
    edges = identifiers(request['protected_edges'], 'protected edge IDs')
    hybrids = identifiers(request['protected_hybrids'], 'protected hybrid IDs')
    require(request['parameter_constraints'] == [],
            'protected coordinate constraints need an exact encoder; no tie may be dropped')
    configs = request['configurations']
    require(type(configs) is list and 1 <= len(configs) <= 32, 'supply 1..32 joint configurations')
    seen, total, support = set(), Fraction(0), []
    for cfg in configs:
        fields(cfg, ['id', 'weight', 'mask'])
        identifiers([cfg['id']], 'configuration ID')
        require(cfg['id'] not in seen, 'duplicate configuration ID')
        seen.add(cfg['id'])
        w = rational(cfg['weight'])
        require(w >= 0, 'negative configuration mass')
        total += w
        mask = cfg['mask']
        require(type(mask) is dict and set(mask) == set(hybrids), 'mask must encode every protected hybrid ID')
        require(all(v is None or (type(v) is int and v in (0, 1)) for v in mask.values()),
                'mask entries are null, 0 or 1')
        if w:
            support.append(cfg['id'])
    require(total == 1, 'joint PMF must sum exactly to 1; no renormalization')
    observations = request['pairs']
    require(type(observations) is list and len(observations) == len(taxa)**2,
            'one supplied certificate for every ordered pair, including diagonal')
    covered, checks = set(), []
    for row in observations:
        fields(row, ['i', 'j', 'certificate'])
        require(type(row['i']) is str and type(row['j']) is str, 'pair IDs must be strings')
        ij = (row['i'], row['j'])
        require(all(i in taxa for i in ij) and ij not in covered, 'unknown or duplicate ordered pair')
        covered.add(ij)
        checks.append(dict(i=ij[0], j=ij[1], **checked(row['certificate'])))
    n, h = len(taxa), len(edges)+len(hybrids)
    cap = max(c['level']-1 for c in checks)
    budget = (2*n-2+2*h)+(8*n-8+6*h)*max(cap-1, 0)
    return dict(schema='supplied_common_menu_result_v1', status='UNKNOWN',
                reason='physical_representative_and_fixed_input_bridge_not_available',
                request_sha256=digest(request), certificate_checks=checks,
                supported_configurations=support, zero_mass_configurations_removed_without_renormalization=True,
                joint_configuration_preserved=True, conditional_support_cap=cap,
                conditional_hybrid_budget=budget, protected_count=h,
                source_existence_certified=False, unknown_size_exclusion_certified=False,
                budget_applied_to_search=False, arbitrary_input_G3_resolved=False,
                remaining_obligations=['authenticate/compile physical representative provider',
                                      'fixed external copy/readout and protected-coordinate encoding',
                                      'same-source law-to-normalized-moment binding',
                                      'complete protected-code admission/parameter feasibility'])


def wire(certificate):
    """Versioned whitespace wire for the Rust checker; no inferred floats."""
    checked(certificate)
    values = ['COMMON_CERT_V1', str(certificate['level'])]
    values.extend(certificate['coefficients'])
    values.extend(certificate['moments'])
    values.append(str(len(certificate['nonnegative_terms'])))
    for t in certificate['nonnegative_terms']:
        values += [t['weight'], str(t['left']), str(t['right']), str(len(t['square']))]+t['square']
    return ' '.join(values)+'\n'
