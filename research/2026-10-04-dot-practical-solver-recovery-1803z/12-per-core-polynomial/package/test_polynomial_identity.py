"""Use the existing source fixture to test the general certificate boundary."""
from pathlib import Path
import copy,json,itertools
from fractions import Fraction as Q
from polynomial_identity import check
from verify_polynomial_identity import replay
from source_checks import root_two_hybrids,compile_source

ROOT=Path(__file__).resolve().parent
def js(x):return x if type(x) is int else [js(v) for v in x]
def terms():
    result=[]
    for sign,i,j in [(1,0,5),(-1,0,4),(-1,1,5),(-1,3,2),(1,3,1),(1,4,2)]:
        powers=[0]*6;powers[i]+=1;powers[j]+=1
        result.append({'coefficient':str(sign),'powers':powers})
    return result
def main():
    source=root_two_hybrids();allocation={t:1 for t in 'abcd'}
    natural=compile_source(source,allocation,'independent')
    first=compile_source(source,allocation,'common',{'H0':0});second=compile_source(source,allocation,'common',{'H0':1})
    union=set(natural)|set(first)|set(second)
    i,j=next((i,j) for i,j in itertools.combinations(sorted(union,key=repr),2)
             if (natural.get(i,Q(0))-second.get(i,Q(0)))*(first.get(j,Q(0))-second.get(j,Q(0)))!=(natural.get(j,Q(0))-second.get(j,Q(0)))*(first.get(i,Q(0))-second.get(i,Q(0))))
    rows=[{'id':name,'forcing':forcing,'readout':'rooted','law':[{'outcome':js(t),'p':str(p)} for t,p in sorted(law.items(),key=lambda x:repr(x[0]))]}
          for name,forcing,law in [('natural',{},natural),('forced0',{'H0':0},first),('forced1',{'H0':1},second)]]
    request={'schema':'source-coupled-polynomial-identity-v1','observation_kind':'exact_unranked_law',
             'source':{'kinds':source.kinds,'taxa':source.taxa,'edges':[{'id':e.name,'u':e.u,'v':e.v} for e in source.edges]},
             'allocation':allocation,'mode':'common','protected_hybrids':['H0'],'protected_edges':[],
             'slots':['h0a','h1b'],'fixed_edges':{e.name:str(e.x) for e in source.edges if e.name not in ('h0a','h1b')},
             'fixed_gammas':{'H1':str(source.gamma['H1'])},'rows':rows,
             'coordinates':[{'row':row,'outcome':js(t)} for row,t in [('natural',i),('forced1',i),('forced0',i),('natural',j),('forced1',j),('forced0',j)]],
             'polynomial':terms(),'limits':{'seconds':30,'max_copy_cap':4}}
    result=check(request);assert result['status']=='FIXED_RETAINED_CORE_ALL_WORDS_UNSAT_BY_POLYNOMIAL_IDENTITY',result
    arithmetic=replay(request,result);assert arithmetic['identity']
    (ROOT/'example-per-core-no.json').write_text(json.dumps(request,indent=2)+'\n')
    (ROOT/'PER-CORE-POLYNOMIAL-CERTIFICATE.json').write_text(json.dumps(result,indent=2)+'\n')
    controls=[]
    for label,edit in [('unknown_complete_flag',lambda r:r.update(complete_core_catalogue=True)),
                       ('empirical_payload',lambda r:r.update(empirical_admission={'status':'ADMITTED'})),
                       ('unknown_ties',lambda r:r.update(parameter_ties=['same-clock'])),
                       ('illegal_nonbridge_word',lambda r:r.update(slots=['ru'])),
                       ('protected_edge_word',lambda r:r.update(protected_edges=['h0a'])),
                       ('unprotected_forcing',lambda r:r['rows'][1].update(forcing={'H1':0})),
                       ('per_row_parameter_refit',lambda r:r['rows'][1].update(fixed_gammas={'H0':'2/3'})),
                       ('malformed_rational_coefficient',lambda r:r['polynomial'][0].update(coefficient='1/0')),
                       ('written_exponent_resource',lambda r:r['polynomial'][0].update(powers=[129,0,0,0,0,0]))]:
        bad=copy.deepcopy(request);edit(bad);answer=check(bad);assert answer['status'].startswith('UNKNOWN'),answer
        controls.append({'label':label,'status':answer['status'],'reason':answer['reason']})
    for label,edit in [('promoted_global_no',lambda r:r.update(global_G3_NO_claimed=True)),
                       ('changed_observed_value',lambda r:r.update(input_polynomial_value='0')),
                       ('changed_compiled_coefficient',lambda r:r['compiled_coordinate_polynomials'][0][0].update(coefficient='999'))]:
        bad=copy.deepcopy(result);edit(bad)
        try:replay(request,bad)
        except ValueError:controls.append({'label':label,'status':'REJECTED_BY_FRACTION_REPLAY'})
        else:raise AssertionError('Tampered coefficient certificate was accepted.')
    independent=copy.deepcopy(request);independent['mode']='independent'
    answer=check(independent);assert answer['status']=='UNKNOWN_AMBIENT_IDENTITY_TEST_INCONCLUSIVE',answer
    controls.append({'label':'COMMON_identity_not_promoted_to_I','status':answer['status']})
    good=copy.deepcopy(request);goodlaw=compile_source(source,allocation,'common')
    good['rows'][0]['law']=[{'outcome':js(t),'p':str(p)} for t,p in goodlaw.items()]
    answer=check(good);assert answer['status']=='UNKNOWN_IDENTITY_CONSISTENT_INPUT',answer
    controls.append({'label':'passing_identity_not_SAT','status':answer['status']})
    alias=copy.deepcopy(request)
    alias['source']['kinds']['h0_0']=alias['source']['kinds'].pop('H0')
    for edge in alias['source']['edges']:
        for endpoint in ('u','v'):
            if edge[endpoint]=='H0':edge[endpoint]='h0_0'
        if edge['id']=='h0a':edge['id']='original-gamma_0'
    alias['protected_hybrids']=['h0_0'];alias['slots'][0]='original-gamma_0'
    for row in alias['rows']:
        if 'H0' in row['forcing']:row['forcing']['h0_0']=row['forcing'].pop('H0')
    answer=check(alias);assert answer['status']==result['status'] and answer['input_polynomial_value']==result['input_polynomial_value'],answer
    replay(alias,answer)
    controls.append({'label':'original_ID_and_parameter_namespace_collision','status':'PASS_CAPTURE_AVOIDING_TYPED_IDENTITIES'})
    out={'status':'PASS_COUPLED_PER_CORE_IDENTITY_AND_INDEPENDENT_FRACTION_REPLAY',
         'identity_example':'Existing protected-COMMON collinearity identity through arbitrary normalized full-forest bridge slots',
         'input_polynomial_value':result['input_polynomial_value'],'namespace_provenance':result['namespace_provenance'],
         'arithmetic_replay':arithmetic,'controls':controls,'global_core_catalogue_or_generic_G3_completion_claimed':False,
         'new_source_census_or_new_mathematical_identity_claimed':False}
    (ROOT/'POLYNOMIAL-IDENTITY-TEST-RECEIPT.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
