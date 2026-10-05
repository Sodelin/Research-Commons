#!/usr/bin/env python3
"""Source coverage and unsupported serializer boundaries, not a new census."""
import copy,json
from pathlib import Path
from assemble_cad_terminal_policy import assemble
from provider_models import models
from verify_algebraic_policy import verify
ROOT=Path(__file__).resolve().parent
def run():
    selector=json.loads((ROOT/'EXPORTED-ACTUAL-TERMINAL-SELECTOR.json').read_text())
    result=json.loads((ROOT/'CAD-ASSEMBLED-POLICY-RECEIPT.json').read_text());policy=result['policy']
    args=(models(),[{'support':[0],'weights':['1','0']}],[0,1],[[0],[1],[0,1]],[['H0'],['H0']],[2,2,1])
    controls=[]
    def unknown(name,candidate):
        out=assemble(args[0],args[1],candidate,*args[2:]);assert out['status']=='UNKNOWN_CAD_WHOLE_POLICY_ASSEMBLY',(name,out)
        controls.append({'name':name,'status':out['status'],'reason':out.get('reason')})
    bad=copy.deepcopy(selector);bad['Export']['coverage']=False;unknown('incomplete_CAD_coverage',bad)
    bad=copy.deepcopy(selector);bad['Export']['soundness'][0]=False;unknown('incomplete_CAD_soundness',bad)
    bad=copy.deepcopy(selector);bad['Export']['cells']=[];unknown('no_complete_selector_cells',bad)
    bad=copy.deepcopy(selector);bad['Export']['cells'][0]['weights'][0]={'kind':'observation','name':'source_gamma'};unknown('hidden_or_nonconstant_action_AST',bad)
    bad=copy.deepcopy(selector);bad['Export']['cells'][0]['guard']={'kind':'comparison','op':'gt','left':{'kind':'root','coefficients':[{'kind':'rational','value':'-1'},{'kind':'rational','value':'1'}],'real_root_index':1},'right':{'kind':'rational','value':'0'}};unknown('general_Root_guard_inlining_pending',bad)
    # Each deleted CAD branch removes actual admissible first histories.
    for removed in range(3):
        changed=copy.deepcopy(policy);changed['next']['branches'].pop(removed)
        out=verify(models(),changed,args[3],args[4],args[5]);assert out['status']=='INVALID_OR_REFUTED_POLICY'
        controls.append({'name':'missing_source_reachable_CAD_cell_'+str(removed),'status':out['status'],'reason':out.get('reason')})
    changed=copy.deepcopy(policy)
    for branch in changed['next']['branches']:
        branch['next']['weights']=['1','0']
    out=verify(models(),changed,args[3],args[4],args[5]);assert out['status']=='INVALID_OR_REFUTED_POLICY'
    controls.append({'name':'invalid_selected_support_action','status':out['status'],'reason':out.get('reason')})
    out=verify(models(),policy,args[3],args[4],[1,2,1]);assert out['status']=='INVALID_OR_REFUTED_POLICY'
    controls.append({'name':'cumulative_PATH_budget','status':out['status'],'reason':out.get('reason')})
    record={'status':'PASS_TERMINAL_CAD_ASSEMBLY_BOUNDARIES','controls':controls,'trust':'whole source-policy verification and bounded serializer controls; SAME_BACKEND'}
    (ROOT/'CAD-ASSEMBLY-BOUNDARY-CONTROLS.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'status':record['status'],'controls':len(controls)}))
if __name__=='__main__':run()
