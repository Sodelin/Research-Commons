"""Fraction-only replay of DELIVERED polynomial identities and input binding.

This independently checks arithmetic, not graph census/source compilation.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json,sys

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def q(x):
    if type(x) is int:return Q(x)
    if not isinstance(x,str):raise ValueError('Exact rational codec required.')
    return Q(x)
def canonical(t):
    if type(t) is int:return t
    if not isinstance(t,list) or len(t)!=2:raise ValueError('Malformed original tree.')
    a,b=canonical(t[0]),canonical(t[1])
    def first(x):return x if type(x) is int else first(x[0])
    return (a,b) if first(a)<first(b) else (b,a)
def key(value,kind):return canonical(value) if kind=='rooted' else tuple(sorted(tuple(sorted(side)) for side in value))
def add(a,b):
    out=dict(a)
    for p,c in b.items():
        out[p]=out.get(p,Q(0))+c
        if not out[p]:del out[p]
    return out
def mul(a,b,max_terms):
    out={}
    for p,c in a.items():
        for r,d in b.items():
            exponent=tuple(x+y for x,y in zip(p,r));out[exponent]=out.get(exponent,Q(0))+c*d
            if not out[exponent]:del out[exponent]
            if len(out)>max_terms:raise ValueError('Replay coefficient resource limit.')
    return out
def power(a,n,dimension,max_terms):
    out={(0,)*dimension:Q(1)}
    while n:
        if n&1:out=mul(out,a,max_terms)
        n//=2
        if n:a=mul(a,a,max_terms)
    return out
def replay(request,certificate):
    if digest(request)!=certificate['input_sha256']:raise ValueError('Original source/profile request binding mismatch.')
    root=Path(__file__).resolve().parent
    expected_files={'symbolic_core.py','polynomial_identity.py','upstream/forest_algebra.py','upstream/source_checks.py'}
    family=request.get('slot_family','normalized_full_forests')
    if family not in ('normalized_full_forests','common_shared_sparse_moments'):raise ValueError('Unencoded slot family.')
    if certificate.get('slot_family',family)!=family:raise ValueError('Changed source-containing slot family.')
    if family=='common_shared_sparse_moments':
        if request['mode']!='common':raise ValueError('COMMON moment family promoted to INDEPENDENT.')
        expected_files.add('common_moment_slots.py')
    if set(certificate['compiler_bindings'])!=expected_files or any(hashlib.sha256((root/name).read_bytes()).hexdigest()!=certificate['compiler_bindings'][name] for name in expected_files):raise ValueError('Delivered compiler/source binding mismatch.')
    if certificate['global_G3_NO_claimed'] is not False or certificate['complete_unknown_size_core_catalogue_verified'] is not False or certificate['positive_realization_or_SAT_claimed'] is not False:raise ValueError('Unsupported scope promotion.')
    if certificate['test_polynomial']!=request['polynomial']:raise ValueError('Polynomial identity changed.')
    dimension=len(certificate['namespace_provenance']);compiled=certificate['compiled_coordinate_polynomials'];coordinates=request['coordinates']
    if len(compiled)!=len(coordinates):raise ValueError('Coordinate shape mismatch.')
    decoded=[]
    for row in compiled:
        poly={}
        for term in row:
            p=tuple(term['powers'])
            if len(p)!=dimension or any(type(n) is not int or n<0 for n in p) or p in poly:raise ValueError('Malformed coefficient carrier.')
            coefficient=q(term['coefficient'])
            if not coefficient:raise ValueError('Zero coefficient must be omitted.')
            poly[p]=coefficient
        decoded.append(poly)
    rows={row['id']:row for row in request['rows']};observed=[]
    for coordinate in coordinates:
        row=rows[coordinate['row']];law={key(v['outcome'],row['readout']):q(v['p']) for v in row['law']}
        observed.append(law.get(key(coordinate['outcome'],row['readout']),Q(0)))
    if [str(x) for x in observed]!=certificate['input_coordinate_values']:raise ValueError('Original labelled input values changed.')
    result={};observed_value=Q(0);max_terms=request.get('limits',{}).get('max_polynomial_terms',200000)
    for term in request['polynomial']:
        coefficient=q(term['coefficient']);powers=term['powers']
        if len(powers)!=len(decoded):raise ValueError('Polynomial coordinate shape mismatch.')
        product={(0,)*dimension:coefficient};point=coefficient
        for row,power_value,value in zip(decoded,powers,observed):
            if type(power_value) is not int or power_value<0:raise ValueError('Malformed polynomial exponent.')
            product=mul(product,power(row,power_value,dimension,max_terms),max_terms);point*=value**power_value
        result=add(result,product);observed_value+=point
    identity=not result
    claim=certificate.get('identity_on_declared_source_containing_slot_family',certificate.get('identity_on_ambient_normalized_forest_rows'))
    if family=='common_shared_sparse_moments' and 'identity_on_ambient_normalized_forest_rows' in certificate:raise ValueError('Moment-family identity cannot be labelled as an arbitrary normalized-row identity.')
    if family=='normalized_full_forests' and certificate.get('identity_on_ambient_normalized_forest_rows') is not identity:raise ValueError('Contradictory normalized-row identity annotation.')
    if claim is not identity or certificate['input_polynomial_value']!=str(observed_value):raise ValueError('Delivered exact polynomial arithmetic mismatch.')
    expected='FIXED_RETAINED_CORE_ALL_WORDS_UNSAT_BY_POLYNOMIAL_IDENTITY' if identity and observed_value else 'UNKNOWN_IDENTITY_CONSISTENT_INPUT' if identity else 'UNKNOWN_AMBIENT_IDENTITY_TEST_INCONCLUSIVE'
    if certificate['status']!=expected:raise ValueError('Certificate verdict contradicts exact replay.')
    return {'status':'PASS_FRACTION_REPLAY_OF_DELIVERED_COEFFICIENT_IDENTITY_AND_ORIGINAL_INPUT',
            'identity':identity,'input_polynomial_value':str(observed_value),
            'source_compiler_fidelity_or_catalogue_completeness_independently_checked':False,
            'generic_global_G3_certificate_accepted':False}

if __name__=='__main__':
    try:print(json.dumps(replay(json.loads(Path(sys.argv[1]).read_text()),json.loads(Path(sys.argv[2]).read_text())),indent=2))
    except (ValueError,TypeError,KeyError,AttributeError,ArithmeticError,RecursionError) as error:
        print(json.dumps({'status':'REJECTED_OR_REPLAY_RESOURCE_LIMIT','reason':str(error)}));sys.exit(1)
