"""The independently reported empty-law bug must fail closed as UNKNOWN."""
import json
from pathlib import Path
from compile_projected_word import compile_policy

ROOT=Path(__file__).resolve().parent

def main():
    cases=[('empty_laws',[{'variables':[],'laws':[],'target':'x'}]),
           ('empty_response',[{'variables':[],'laws':[[]],'target':'x'}]),
           ('nonsequence_laws',[{'variables':[],'laws':None,'target':'x'}]),
           ('empty_model_carrier',[])]
    results=[]
    for label,models in cases:
        result=compile_policy(models,[{'support':[0],'weights':['1']}],[[0]],[[]],[1,1,0])
        assert result['status']=='UNKNOWN_UNSUPPORTED_OR_RESOURCE_LIMIT',(label,result['status'])
        assert result['mathematical_budget_NO_claimed'] is False
        results.append({'control':label,'result':result})
    output={'status':'PASS_FRESH_EMPTY_AND_MALFORMED_CARRIER_UNKNOWN_BOUNDARY',
            'regression_prior_manifest':'31ccfdbec0d278bb249dce3123fc004bce48377883cd168cb19827ecb15ac332',
            'results':results,'projection_mathematics_changed':False}
    (ROOT/'FRESH-CARRIER-PREFLIGHT-RECEIPT.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({'status':output['status'],'controls':len(results)},indent=2))

if __name__=='__main__':main()
