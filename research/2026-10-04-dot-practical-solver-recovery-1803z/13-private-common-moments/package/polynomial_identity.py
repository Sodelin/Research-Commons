"""Source-coupled, per-retained-core polynomial NO certificates.

The ambient normalized full-forest slot test is deliberately stronger than
testing actual words. It is sound when it passes and incomplete when it fails.
A complete unknown-size core catalogue is NOT implemented by this adapter.
"""
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import hashlib,json,signal,sys
import sympy as sp
import networkx as nx
from symbolic_core import compile_core
from source_checks import Source,Edge,quartet
from forest_algebra import forests,forest,tree,leaves

class Unsupported(ValueError):pass
class ResourceLimit(Exception):pass

def canonical_json(value):return json.dumps(value,sort_keys=True,separators=(',',':')).encode()
def digest(value):return hashlib.sha256(canonical_json(value)).hexdigest()
def rational(value):
    if type(value) is int:return Fraction(value)
    if not isinstance(value,str):raise Unsupported('Exact rational strings/integers required; empirical probabilities are not admitted.')
    return Fraction(value)
def original_tree(value,cap,depth=0):
    if depth>64:raise Unsupported('Outcome expression nesting limit64 exceeded.')
    if type(value) is int and 0<=value<cap:return value
    if isinstance(value,list) and len(value)==2:return tree(original_tree(value[0],cap,depth+1),original_tree(value[1],cap,depth+1))
    raise Unsupported('Rooted outcome must retain original integer copy labels and binary child structure.')
def outcome(value,kind,cap):
    if kind=='rooted':
        result=original_tree(value,cap)
        if leaves(result)!=tuple(range(cap)):raise Unsupported('Each original copy occurs exactly once in a complete rooted outcome.')
        return result
    if kind=='quartet':
        if cap!=4 or not isinstance(value,list) or len(value)!=2 or any(not isinstance(v,list) or len(v)!=2 for v in value):raise Unsupported('Quartet outcome requires the complete four original copy labels.')
        if any(type(v) is not int for side in value for v in side) or sorted(sum(value,[]))!=list(range(4)):raise Unsupported('Quartet sides must partition original copies0..3.')
        return tuple(sorted(tuple(sorted(side)) for side in value))
    raise Unsupported('Only actual rooted unranked and original-labelled quartet readouts are implemented.')

def prepare(request):
    allowed={'schema','observation_kind','source','allocation','mode','protected_hybrids','protected_edges','slots','fixed_edges','fixed_gammas','rows','coordinates','polynomial','limits','empirical_admission','parameter_ties','complete_core_catalogue','slot_family'}
    if not isinstance(request,dict) or set(request)-allowed:raise Unsupported('Unencoded request fields.')
    if request.get('schema')!='source-coupled-polynomial-identity-v1' or request.get('observation_kind')!='exact_unranked_law':raise Unsupported('This interface requires declared exact source genealogy laws.')
    if request.get('empirical_admission') or request.get('parameter_ties'):raise Unsupported('Scientific adapters or extra parameter ties require their actual encoder.')
    # No supplied flag can grant global catalogue coverage.
    if request.get('complete_core_catalogue'):raise Unsupported('No complete retained-core catalogue validator is implemented; supplied coverage flags cannot authorize global NO.')
    description=request['source']
    if set(description)!={'kinds','taxa','edges'}:raise Unsupported('Actual source description must include kinds/taxa/original edge IDs.')
    edges=tuple(Edge(e['id'],e['u'],e['v'],Fraction(1,2)) for e in description['edges'])
    if any(set(e)!={'id','u','v'} for e in description['edges']):raise Unsupported('Unexpected edge field.')
    source=Source(description['kinds'],description['taxa'],edges,{v:Fraction(1,2) for v,k in description['kinds'].items() if k=='hybrid'})
    admission=source.validate();mode=request['mode']
    if mode not in ('common','independent'):raise Unsupported('One fixed inheritance mechanism must be declared.')
    family=request.get('slot_family','normalized_full_forests')
    if family not in ('normalized_full_forests','common_shared_sparse_moments'):raise Unsupported('Unencoded source-containing slot family.')
    if family=='common_shared_sparse_moments' and mode!='common':raise Unsupported('COMMON time-change moments cannot replace INDEPENDENT forest kernels.')
    allocation=request['allocation']
    if set(allocation)!=set(source.taxa.values()) or any(type(n) is not int or n<1 for n in allocation.values()):raise Unsupported('This interface requires one fixed positive allocation for every original taxon.')
    cap=sum(allocation.values());limits=request.get('limits',{})
    if not isinstance(limits,dict) or set(limits)-{'seconds','max_copy_cap','max_polynomial_terms'}:raise Unsupported('Unrecognized resource limit.')
    max_cap=limits.get('max_copy_cap',5);terms=limits.get('max_polynomial_terms',200000);seconds=limits.get('seconds',30)
    if any(type(x) is not int or x<1 for x in (max_cap,terms,seconds)) or seconds>300:raise Unsupported('Resource ceilings must be positive integers; seconds≤300.')
    if cap>max_cap:raise Unsupported('Declared machine copy-cap ceiling exceeded; not a mathematical stopping bound.')
    protected=request.get('protected_hybrids',[]);protected_edges=request.get('protected_edges',[]);slots=request.get('slots',[])
    for value in (protected,protected_edges,slots):
        if not isinstance(value,list) or len(set(value))!=len(value) or any(not isinstance(x,str) for x in value):raise Unsupported('Original IDs must be distinct strings in explicit lists.')
    if not set(protected)<=set(source.gamma) or not set(protected_edges)<={e.name for e in edges}:raise Unsupported('Unknown protected original identity.')
    if set(slots)&set(protected_edges):raise Unsupported('A protected original edge cannot become a fresh word slot.')
    for name in slots:
        edge=next((e for e in edges if e.name==name),None)
        if edge is None:raise Unsupported('Unknown original slot edge.')
        graph=source.graph().to_undirected();graph.remove_edge(edge.u,edge.v,key=edge.name)
        if nx.has_path(graph,edge.u,edge.v):raise Unsupported('Fresh source words may occupy actual unmarked bridges only.')
    fixed_edges=request.get('fixed_edges',{});fixed_gammas=request.get('fixed_gammas',{})
    if not set(fixed_edges)<={e.name for e in edges} or set(fixed_edges)&set(slots) or not set(fixed_gammas)<=set(source.gamma):raise Unsupported('Unknown/conflicting original fixed parameter identity.')
    for value in [*fixed_edges.values(),*fixed_gammas.values()]:
        if not 0<rational(value)<1:raise Unsupported('Every natural finite edge/gamma parameter remains strict-interior.')
    rows=request['rows']
    if not isinstance(rows,list) or not rows or len({row['id'] for row in rows})!=len(rows):raise Unsupported('Distinct declared profile row IDs required.')
    for row in rows:
        if set(row)!={'id','forcing','readout','law'} or not isinstance(row['id'],str):raise Unsupported('Each row includes original ID, forcing, authorized readout and complete law.')
        if not set(row['forcing'])<=set(protected) or any(type(b) is not int or b not in (0,1) for b in row['forcing'].values()):raise Unsupported('Control may address protected original hybrids only.')
        if row['readout'] not in ('rooted','quartet'):raise Unsupported('Unencoded readout.')
        law={}
        for event in row['law']:
            if set(event)!={'outcome','p'}:raise Unsupported('Law events have outcome and exact p fields.')
            key=outcome(event['outcome'],row['readout'],cap);p=rational(event['p'])
            if key in law or not 0<=p<=1:raise Unsupported('Duplicate or nonprobability law event.')
            law[key]=p
        if sum(law.values())!=1:raise Unsupported('Every supplied complete law must normalize exactly.')
        row['parsed_law']=law
    coordinates=request['coordinates'];row_ids={row['id']:row for row in rows};keys=[]
    for c in coordinates:
        if set(c)!={'row','outcome'} or c['row'] not in row_ids:raise Unsupported('Coordinate must bind one actual row/outcome.')
        keys.append((c['row'],outcome(c['outcome'],row_ids[c['row']]['readout'],cap)))
    if not keys or len(set(keys))!=len(keys):raise Unsupported('Polynomial coordinates must be distinct and nonempty.')
    monomials=[]
    for term in request['polynomial']:
        if set(term)!={'coefficient','powers'} or not isinstance(term['powers'],list) or len(term['powers'])!=len(keys) or any(type(n) is not int or n<0 for n in term['powers']):raise Unsupported('Polynomial term must use exact coefficient and one nonnegative exponent per declared coordinate.')
        if any(n>128 for n in term['powers']):raise Unsupported('Written polynomial exponent machine ceiling128 exceeded; UNKNOWN, not an algebraic NO.')
        monomials.append((rational(term['coefficient']),tuple(term['powers'])))
    return source,admission,allocation,cap,mode,family,protected_edges,slots,fixed_edges,fixed_gammas,rows,keys,monomials,terms,seconds

def compile_certificate(request):
    # Preserve the exact input rather than adding parsed fields to its identity.
    input_hash=digest(request);request=json.loads(json.dumps(request))
    source,admission,allocation,cap,mode,family,protected_edges,slots,fixed_edges,fixed_gammas,rows,keys,monomials,max_terms,seconds=prepare(request)
    symbols=[];provenance=[]
    def fresh(role,owner,index):
        symbol=sp.Dummy(f'{role}_{len(symbols)}');symbols.append(symbol)
        provenance.append({'index':len(symbols)-1,'typed_identity':[role,owner,index]})
        return symbol
    edges={e.name:(sp.Rational(rational(fixed_edges[e.name]).numerator,rational(fixed_edges[e.name]).denominator) if e.name in fixed_edges else fresh('source-edge',e.name,0)) for e in source.edges if e.name not in slots}
    gamma={h:(sp.Rational(rational(fixed_gammas[h]).numerator,rational(fixed_gammas[h]).denominator) if h in fixed_gammas else fresh('original-gamma',h,0)) for h in sorted(source.gamma)}
    slot_rows={};slot_provenance=[]
    for name in slots:
        edge=next((e for e in source.edges if e.name==name),None)
        if edge is None:raise Unsupported('Unknown original slot edge.')
        graph=source.graph();desc=nx.descendants(graph,edge.v)|{edge.v}
        bound=sum(allocation[t] for v,t in source.taxa.items() if v in desc)
        if family=='common_shared_sparse_moments':
            from common_moment_slots import shared_moment_rows
            shared_rows,_=shared_moment_rows(bound,name,fresh)
            for k,row in shared_rows.items():slot_rows[name,k]=row
        else:
            for k in range(bound+1):
                outcomes=forests(tuple(range(k)));row={}
                for i,f in enumerate(outcomes[:-1]):row[f]=fresh('slot-forest',[name,k],i)
                row[outcomes[-1]]=1-sum(row.values());slot_rows[name,k]=row
        slot_provenance.append({'original_edge_id':name,'maximum_current_roots':bound,
            'derived_from':'sum of copies on actual descendant taxon side of a bridge',
            'kernel_domain':('ONE sparse-moment family shared across ALL arities and profile rows; contains every actual private-COMMON bridge word' if family=='common_shared_sparse_moments' else 'ALL normalized full labelled forest rows; contains every positive actual source word; signed values are test variables only')})
    def kernel(name):
        def get(k):
            if (name,k) not in slot_rows:raise Unsupported('Actual source exceeded its graph-derived descendant copy bound.')
            return slot_rows[name,k]
        return get
    actual={};coordinate_polynomials=[]
    for row in rows:
        law=compile_core(source,allocation,mode,row['forcing'],edges,gamma,{name:kernel(name) for name in slots},protected_edges)
        if row['readout']=='quartet':
            projected=defaultdict(lambda:sp.S.Zero)
            for t,p in law.items():projected[quartet(t)]+=p
            law=dict(projected)
        actual[row['id']]=law
    symbolic_coordinates=[actual[row].get(key,sp.S.Zero) for row,key in keys]
    observed=[next(r for r in rows if r['id']==row)['parsed_law'].get(key,Fraction(0)) for row,key in keys]
    polynomial=sum(sp.Rational(c.numerator,c.denominator)*sp.prod(y**n for y,n in zip(symbolic_coordinates,powers)) for c,powers in monomials)
    if symbols:residual=sp.Poly(polynomial,*symbols,domain=sp.QQ)
    else:residual=sp.Poly(polynomial,sp.Dummy('constant'),domain=sp.QQ)
    if len(residual.terms())>max_terms:raise Unsupported('Polynomial coefficient resource ceiling exceeded.')
    observed_value=sum(c*__import__('functools').reduce(lambda a,b:a*b,(x**n for x,n in zip(observed,powers)),Fraction(1)) for c,powers in monomials)
    for expr in symbolic_coordinates:
        poly=sp.Poly(expr,*symbols,domain=sp.QQ) if symbols else sp.Poly(expr,sp.Dummy('constant'),domain=sp.QQ)
        if len(poly.terms())>max_terms:raise Unsupported('Delivered coefficient resource ceiling exceeded.')
        coordinate_polynomials.append([{'powers':list(powers) if symbols else [],'coefficient':str(coefficient)} for powers,coefficient in poly.terms() if coefficient])
    identity=residual.is_zero
    status=('FIXED_RETAINED_CORE_ALL_WORDS_UNSAT_BY_POLYNOMIAL_IDENTITY' if identity and observed_value!=0 else 'UNKNOWN_IDENTITY_CONSISTENT_INPUT' if identity else 'UNKNOWN_AMBIENT_IDENTITY_TEST_INCONCLUSIVE')
    return {'schema':'per-core-source-polynomial-identity-certificate-v2','status':status,'input_sha256':input_hash,
        'compiler_bindings':{name:hashlib.sha256((Path(__file__).resolve().parent/name).read_bytes()).hexdigest()
            for name in ('symbolic_core.py','polynomial_identity.py','upstream/forest_algebra.py','upstream/source_checks.py')+ (('common_moment_slots.py',) if family=='common_shared_sparse_moments' else ())},
        'source_admission':admission,'mode':mode,'original_rows_share_one_parameter_and_word_assignment':True,
        'namespace_provenance':provenance,'slot_provenance':slot_provenance,
        'compiled_coordinate_polynomials':coordinate_polynomials,'input_coordinate_values':[str(v) for v in observed],
        'test_polynomial':request['polynomial'],'slot_family':family,
        'identity_on_declared_source_containing_slot_family':bool(identity),
        **({'identity_on_ambient_normalized_forest_rows':bool(identity)} if family=='normalized_full_forests' else {}),
        'input_polynomial_value':str(observed_value),'complete_unknown_size_core_catalogue_verified':False,
        'global_G3_NO_claimed':False,'positive_realization_or_SAT_claimed':False,
        'scope':'Only this original retained core, fixed declared background constraints and legal unmarked bridge expansions; stronger ambient coefficient test is incomplete for actual-word identities.'}

def check(request):
    old_handler=None;old_timer=None
    try:
        seconds=request.get('limits',{}).get('seconds',30) if isinstance(request,dict) else 30
        if type(seconds) is not int or not 0<seconds<=300:raise Unsupported('Invalid bounded runtime.')
        def timeout(signum,frame):raise ResourceLimit('Source/identity computation resource timeout; UNKNOWN.')
        old_handler=signal.signal(signal.SIGALRM,timeout);old_timer=signal.setitimer(signal.ITIMER_REAL,seconds)
        return compile_certificate(request)
    except (Unsupported,ValueError,TypeError,KeyError,AttributeError,ArithmeticError,RecursionError,MemoryError,ResourceLimit,sp.PolynomialError,nx.NetworkXException) as error:
        return {'status':'UNKNOWN_UNSUPPORTED_OR_RESOURCE_LIMIT','reason':str(error),'global_G3_NO_claimed':False,'positive_realization_or_SAT_claimed':False}
    finally:
        if old_handler is not None:
            signal.setitimer(signal.ITIMER_REAL,0);signal.signal(signal.SIGALRM,old_handler)
            if old_timer and old_timer[0]>0:signal.setitimer(signal.ITIMER_REAL,*old_timer)

if __name__=='__main__':
    request=json.loads(Path(sys.argv[1]).read_text());result=check(request)
    text=json.dumps(result,indent=2)+'\n'
    if len(sys.argv)>2:Path(sys.argv[2]).write_text(text)
    else:print(text,end='')
