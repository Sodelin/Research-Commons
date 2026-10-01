"""Finite controls for the matched original-H resource substitution theorem.

Independent graph construction/admission/target checks. Exact topology-law
comparisons reuse the pinned, separately reviewed G7 supplied-source compiler;
they do not claim a full calendar density compilation.
"""
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as F
from itertools import permutations
import ast, hashlib, json, sys, time
import sympy as sp

START=time.perf_counter()
HERE=Path(__file__).resolve().parent
# The canonical Commons checkout is preferred. The second path is only the
# existing scratch layout used by the original execution before publication.
SOURCE=HERE.parent/'2026-10-01-g7-continuous-design'
if not (SOURCE/'law_compiler.py').is_file():
    SOURCE=HERE.parent/'sol61-head-audit'/'g7'
raw=(SOURCE/'law_compiler.py').read_bytes()
compiler_blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
assert compiler_blob=='0fed445a5b7f72ebe056f8b8778d8e67dcc898e2'
sys.path.insert(0,str(SOURCE))
from law_compiler import Network, compile_law

# Read only the pure independently authored helper definitions. Importing its
# whole script would rerun/overwrite the original CG2 execution receipt.
src=ast.parse((HERE/'independent_checks.py').read_text())
helpers={'rooted_trees','tree_graph','reach','splits','insert','audit_source'}
sel=ast.Module(body=[n for n in src.body if isinstance(n,ast.FunctionDef) and n.name in helpers],type_ignores=[])
exec(compile(sel,'CG2-independent-graph-helpers','exec'),globals())

def neutral(edges,ages,rates,b,h,d):
    pb=next(u for u,v in edges if v==b)
    ee=tuple(e for e in edges if e!=(pb,b))+((pb,'@P'),('@P','@H'),('@P','@H'),('@H',b))
    aa={**ages,'@P':d,'@H':h}
    rr={e:r for e,r in rates.items() if e!=(pb,b)}
    rr.update({(pb,'@P'):rates[pb,b],('@P','@H'):rates[pb,b],('@H',b):rates[pb,b]})
    return ee,aa,rr

def forced_edges(edges,bit):
    incoming=[i for i,(u,v) in enumerate(edges) if v=='@H']
    assert len(incoming)==2
    return tuple(e for i,e in enumerate(edges) if i!=incoming[1-bit])

def law(edges,ages,root,labels,mode='independent',bit=None,eps=sp.Rational(1,10),samples=None):
    # One fixed positive calendar clock for all rows: pair rate -3*log(3/4).
    # All node ages are multiples of 1/3, so exp(-rho*duration) is rational.
    z=sp.Rational(3,4)
    vals={}
    for i,(u,v) in enumerate(edges):
        power=3*(ages[u]-ages[v]); assert power.denominator==1 and power>0
        vals[i]=z**int(power)
    net=Network(tuple(edges),root,labels)
    force={} if bit is None else {'@H':bit}
    # The pinned compiler's gamma is probability of incoming occurrence 0;
    # epsilon in the proof is the RARE occurrence-1 probability.
    inherit={} if '@H' not in ages else {'@H':1-eps}
    return compile_law(net,mode,force,samples=samples,edge_values=vals,inheritance_values=inherit)

def equal(a,b):
    return all(sp.expand(a.get(t,0)-b.get(t,0))==0 for t in set(a)|set(b))

sources=0; strict_pairs=0; forced_target_checks=0; compiler_calls=0; full_vector_equalities=0
labels=tuple('ABCD'); examples=[]
for t in rooted_trees(labels):
    edges,ages,rates,root=tree_graph(t); target=splits(edges,labels)
    base=law(edges,ages,root,labels); compiler_calls+=1
    for a,b in permutations(labels,2):
        sigma=frozenset((frozenset((a,b)),frozenset(set(labels)-{a,b})))
        if sigma in target:
            continue
        ee,ea,er,(pa,pb,h,d)=insert(edges,ages,rates,a,b)
        be,ba,br=neutral(edges,ages,rates,b,h,d)
        audit_source(ee,ea,er,root,labels); audit_source(be,ba,br,root,labels); sources+=2
        assert (tuple(e for e in ee if e[1]=='@H')[0][0],tuple(e for e in ee if e[1]=='@H')[1][0])==(pb,'@D')
        assert tuple(e for e in be if e[1]=='@H')==(('@P','@H'),('@P','@H'))
        assert er['@H',b]==br['@H',b]==rates[pb,b]
        assert ea['@H']==ba['@H']==h
        for bit in (0,1):
            assert splits(forced_edges(be,bit),labels)==target
            et=splits(forced_edges(ee,bit),labels)
            assert et==target if bit==0 else sigma in et
            forced_target_checks+=2
        assert target | splits(forced_edges(ee,1),labels)>target
        strict_pairs+=1
        if len(examples)<2:
            examples.append((edges,ages,rates,root,a,b,ee,ea,be,ba))
        forced_effective={bit:law(ee,ea,root,labels,bit=bit) for bit in (0,1)}
        forced_neutral={bit:law(be,ba,root,labels,bit=bit) for bit in (0,1)}
        compiler_calls+=4
        assert equal(forced_effective[0],base)
        assert equal(forced_neutral[0],base) and equal(forced_neutral[1],base)
        full_vector_equalities+=3
        for eps in (sp.Rational(1,100),sp.Rational(1,10),sp.Rational(1,2)):
            mixture={s:(1-eps)*base.get(s,0)+eps*forced_effective[1].get(s,0) for s in set(base)|set(forced_effective[1])}
            for mode in ('independent','common'):
                el=law(ee,ea,root,labels,mode,eps=eps)
                bl=law(be,ba,root,labels,mode,eps=eps)
                compiler_calls+=2
                assert equal(el,mixture) and equal(bl,base)
                full_vector_equalities+=2

multicopy_cases=0; neutral_ind_difference_controls=0; changed_coordinates=[]
for edges,ages,rates,root,a,b,ee,ea,be,ba in examples:
    samples={x:(x+'0',) for x in labels};samples[b]=(b+'0',b+'1')
    base=law(edges,ages,root,labels,samples=samples);compiler_calls+=1
    for mode in ('independent','common'):
        for bit in (0,1):
            bl=law(be,ba,root,labels,mode,bit=bit,samples=samples)
            compiler_calls+=1
            assert equal(bl,base);full_vector_equalities+=1
            multicopy_cases+=1
        el=law(ee,ea,root,labels,mode,bit=0,samples=samples)
        compiler_calls+=1
        assert equal(el,base);full_vector_equalities+=1;multicopy_cases+=1
        bl=law(be,ba,root,labels,mode,samples=samples);compiler_calls+=1
        if mode=='common':
            assert equal(bl,base);full_vector_equalities+=1
        else:
            assert not equal(bl,base);neutral_ind_difference_controls+=1
            s=next(s for s in set(bl)|set(base) if sp.expand(bl.get(s,0)-base.get(s,0))!=0)
            changed_coordinates.append({'rooted_topology':repr(s),'neutral_minus_tree':str(sp.expand(bl.get(s,0)-base.get(s,0)))})

result={'status':'PASS','python':sys.version.split()[0],'sympy':sp.__version__,
 'original_labelled_rooted_trees_n4':len(rooted_trees(labels)),
 'strict_absent_cherry_same_registry_pairs':strict_pairs,
 'positive_admitted_source_graphs_checked':sources,
 'forced_source_target_comparisons':forced_target_checks,
 'exact_complete_rooted_topology_law_compilations':compiler_calls,
 'exact_complete_response_vector_equality_checks':full_vector_equalities,
 'five_copy_full_forcing_equality_cases':multicopy_cases,
 'neutral_independent_natural_not_tree_controls':neutral_ind_difference_controls,
 'negative_control_changed_coordinates':changed_coordinates,
 'one_shared_calendar_assignment':'all nodes retain original ages; h=u/3,d=2u/3; every original/inserted population pair rate=-3*log(3/4); all row survivals=(3/4)^(3*calendar_duration)',
 'pinned_compiler_git_blob':compiler_blob,
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'seconds':time.perf_counter()-START,
 'limits':'Finite graph/source and full rooted-topology response controls, not full calendar density execution. Uniform arbitrary parameters/all-copy/stopping/resource conclusions are hand proofs in RESOURCE-SUBSTITUTION.md. No physical actuator, sequence calibration, formal proof, historical novelty or unrestricted G7 optimum.'}
Path(__file__).with_name('resource-substitution-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
