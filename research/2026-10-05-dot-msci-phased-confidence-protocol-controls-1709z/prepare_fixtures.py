"""Declare deterministic protocol records only; no biological sampling or inference."""
import copy,json
from pathlib import Path
import integration_core as c
BASE=Path(__file__).resolve().parent

def write(path,value):
    raw=c.canonical(value);path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('xb') as out:out.write(raw)
    return c.sha(raw)
def literal_panel():return {'schema':'complete-six-copy-two-site-loci-v1','loci':[{'id':'locus1','columns':[1,2],'calls':{k:'AA' for k in c.LABELS}},{'id':'locus2','columns':[3,7],'calls':dict(A1='AG',A2='CA',B1='GA',B2='TT',C1='CT',C2='GG')}]}
def identical(m):return {'schema':'complete-six-copy-two-site-loci-v1','loci':[{'id':f'protocol_{i:03d}','columns':[1,2],'calls':{k:'AA' for k in c.LABELS}} for i in range(m)]}
def selection(data):return c.sha(c.canonical([{'id':x['id'],'columns':x['columns']} for x in data['loci']]))
def prepare(folder):
    folder=Path(folder);folder.mkdir(exist_ok=False)
    prior=c.read(c.PROVIDER/'declared-requests/distinct.json','a73fc025632555e058b8dc6f2c1440e6f625409caefd36ae56b660f0ba79cedb')
    cases=[('literal_two',literal_panel(),'1/10',0,True,'PROTOCOL_ONLY_UNKNOWN_CONDITIONAL_OUTER_COVER'),('correlated_twelve',identical(12),'1/10',2,True,'PROTOCOL_ONLY_UNKNOWN_CONDITIONAL_OUTER_COVER'),('stricter_delta',identical(12),'1/1000',2,True,'PROTOCOL_ONLY_UNKNOWN_CONDITIONAL_OUTER_COVER'),('incompatible_sixtyfour',identical(64),'1/10',1,True,'PROTOCOL_ONLY_CONDITIONAL_INCOMPATIBILITY'),('malformed_late',literal_panel(),'1/10',0,True,'EVIDENCE_INVALID'),('partial_stream',literal_panel(),'1/10',0,True,'EVIDENCE_INVALID'),('unregistered',literal_panel(),'1/10',0,False,'NOT_ADMITTED')]
    entries=[];registry={'schema':'externally-reviewed-admission-registry-v1','admissions':{}}
    for name,data,delta,stages,registered,status in cases:
        expected_m=len(data['loci']);selection_sha=selection(data)
        if name=='incompatible_sixtyfour':
            for locus in data['loci']:locus['calls']['B1']='GA'
        if name=='malformed_late':data['loci'][-1]['calls']['A1']='AN'
        if name=='partial_stream':data['loci'].pop()
        root=folder/name;dataset_sha=write(root/'DATASET.json',data)
        budget=dict(prior['budget']);budget.update(max_stages=stages,max_splits=0,max_states=1,max_depth=0,wall_ms=10000,recovery_wall_ms=10000,recovery_max_stages=stages)
        request={'schema':'phased-nine-feature-analysis-v1','dataset_sha256':dataset_sha,'admission_sha256':'pending','delta':delta,'domain':prior['box'],'normalized_width_targets':prior['normalized_width_targets'],'inverse_budget':budget,'radius_steps':16,'expected_loci':expected_m,'selection_sha256':selection_sha,'provenance':{'kind':'hand_constructed_protocol_fixture','biological_sampling_claimed':False,'name':name}}
        admission={'schema':'reviewed-phased-design-v1','model':c.MODEL,'dataset_sha256':dataset_sha,'analysis_premises_sha256':c.premise_identity(request),'selection_sha256':selection_sha,'locus_count':expected_m,'classification':'protocol_fixture','premises':{key:'not_asserted_protocol_fixture' for key in ('A1','A2','A3','A4','A5','A6')},'review_notes':'Protocol case '+name+'; no scientific admission or empirical coverage claim. Negative syntax cases are deliberate tests.'}
        admission_sha=write(root/'ADMISSION.json',admission);request['admission_sha256']=admission_sha;request_sha=write(root/'REQUEST.json',request)
        if registered:registry['admissions'][admission_sha]={'classification':'protocol_fixture','review_scope':'protocol_semantics_only'}
        expected_counts=None
        if name=='literal_two':expected_counts=dict(AC1=2,AC2=2,CC1=1,BC1=1,BC2=2,AB1=1,AB2=2,AA1=2,BB1=2)
        elif name in ('correlated_twelve','stricter_delta'):expected_counts={key:expected_m for key in c.FEATURES}
        elif name=='incompatible_sixtyfour':expected_counts={key:(expected_m if key in ('AC1','AC2','CC1','AA1') else 0) for key in c.FEATURES}
        entries.append({'name':name,'request':name+'/REQUEST.json','request_sha256':request_sha,'dataset':name+'/DATASET.json','dataset_sha256':dataset_sha,'admission':name+'/ADMISSION.json','admission_sha256':admission_sha,'expected_status':status,'expected_counts':expected_counts,'registered_protocol':registered})
    registry_sha=write(folder/'ADMISSION-REGISTRY.json',registry)
    identity=write(folder/'CONTROL-MANIFEST.json',{'schema':'seven-protocol-controls-v1','controls':entries,'admission_registry_sha256':registry_sha,'all_scientific_admission_withheld':True,'biological_simulation_or_sampling':False})
    return identity,registry_sha
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);a=p.parse_args();print(json.dumps(prepare(a.output)))
