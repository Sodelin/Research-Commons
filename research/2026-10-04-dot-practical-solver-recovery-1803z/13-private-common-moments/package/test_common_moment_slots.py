"""Reuse exact COMMON time-change providers; retain full forest/source rows."""
from pathlib import Path
from fractions import Fraction as Q
import copy,json
import sympy as sp
from common_moment_slots import shared_moment_rows,actual_word_moments
from polynomial_identity import check
from verify_polynomial_identity import replay
from forest_algebra import ForestAlgebra,tree
from source_checks import caterpillar,compile_source
ROOT=Path(__file__).resolve().parent

def js(t):return t if type(t) is int else [js(v) for v in t]

def main():
    alg=ForestAlgebra(4);lead=Q(2,3)
    cells=((Q(1,3),Q(3,5),Q(2,7),Q(4,5)),(Q(2,5),Q(5,7),Q(3,8),Q(3,4)))
    atoms,moments=actual_word_moments(alg,lead,cells)
    variables={}
    def fresh(role,owner,index):
        value=sp.Dummy('shared_common_moment');variables[owner[1]]=value;return value
    rows,_=shared_moment_rows(4,'one-original-slot',fresh)
    assignment={symbol:sp.Rational(moments[j*(j-1)//2].numerator,moments[j*(j-1)//2].denominator) for j,symbol in variables.items()}
    actual=alg.edge(lead)
    for x,y,g,a in cells:actual=alg.mul(actual,alg.cell(x,y,g,a,'common'))
    for i,(k,f) in enumerate(alg.coords):assert sp.expand(rows[k][f].subs(assignment))==sp.Rational(actual[i].numerator,actual[i].denominator)
    assert sum(atoms.values())==1 and all(0<x<1 and p>0 for x,p in atoms.items())
    source=caterpillar();other=caterpillar();other.taxa={v:('c' if t=='a' else 'a' if t=='c' else t) for v,t in other.taxa.items()}
    observed=compile_source(other,{t:1 for t in 'abcd'},'common')
    first=tree(tree(tree(0,2),1),3);second=tree(tree(tree(1,2),0),3)
    request={'schema':'source-coupled-polynomial-identity-v1','observation_kind':'exact_unranked_law',
             'source':{'kinds':source.kinds,'taxa':source.taxa,'edges':[{'id':e.name,'u':e.u,'v':e.v} for e in source.edges]},
             'allocation':{t:1 for t in 'abcd'},'mode':'common','protected_hybrids':[],'protected_edges':[],
             'slots':['rb'],'fixed_edges':{e.name:str(e.x) for e in source.edges if e.name!='rb'},
             'rows':[{'id':'passive','forcing':{},'readout':'rooted','law':[{'outcome':js(t),'p':str(p)} for t,p in sorted(observed.items(),key=lambda x:repr(x[0]))]}],
             'coordinates':[{'row':'passive','outcome':js(first)},{'row':'passive','outcome':js(second)}],
             'polynomial':[{'coefficient':'1','powers':[1,0]},{'coefficient':'-1','powers':[0,1]}],
             'limits':{'seconds':30,'max_copy_cap':4}}
    coarse=check(request);assert coarse['status']=='UNKNOWN_AMBIENT_IDENTITY_TEST_INCONCLUSIVE',coarse
    request['slot_family']='common_shared_sparse_moments';tight=check(request)
    assert tight['status']=='FIXED_RETAINED_CORE_ALL_WORDS_UNSAT_BY_POLYNOMIAL_IDENTITY',tight
    assert tight['slot_provenance'][0]['maximum_current_roots']==3
    assert 'identity_on_ambient_normalized_forest_rows' not in tight
    arithmetic=replay(request,tight)
    bad=copy.deepcopy(request);bad['mode']='independent';rejected=check(bad);assert rejected['status'].startswith('UNKNOWN'),rejected
    (ROOT/'example-common-moment-per-core-no.json').write_text(json.dumps(request,indent=2)+'\n')
    (ROOT/'COMMON-MOMENT-PER-CORE-CERTIFICATE.json').write_text(json.dumps(tight,indent=2)+'\n')
    out={'status':'PASS_SHARED_COMMON_MOMENT_FULL_FOREST_AND_ACTUAL_CORE_IDENTITY',
         'complete_labelled_forest_coordinates_reconstructed':alg.dim,'one_moment_assignment_shared_across_all_arities':True,
         'actual_private_coin_atom_law':{str(x):str(p) for x,p in sorted(atoms.items())},
         'coarse_family_status':coarse['status'],'tight_COMMON_family_status':tight['status'],
         'input_polynomial_value':tight['input_polynomial_value'],'fraction_replay':arithmetic,
         'INDEPENDENT_substitution_status':rejected['status'],'global_G3_NO_claimed':False,
         'new_COMMON_closure_or_positive_realization_theorem_claimed':False,
         'source_control':'Existing caterpillar and a label permutation; no source census enlargement'}
    (ROOT/'COMMON-MOMENT-TEST-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))

if __name__=='__main__':main()
