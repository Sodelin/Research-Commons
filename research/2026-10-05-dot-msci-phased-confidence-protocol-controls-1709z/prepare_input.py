"""Bounded preparation: no inverse action before complete admitted extraction."""
import json
from pathlib import Path
import integration_core as c

def write_new(path,value):
    raw=c.canonical(value)
    with Path(path).open('xb') as out:out.write(raw)
    return c.sha(raw)

def prepare(request_path,request_sha,dataset_path,admission_path,registry_path,registry_sha,outdir):
    outdir=Path(outdir);outdir.mkdir(exist_ok=False)
    try:
        req,delta=c.request(request_path,request_sha)
        admitted=c.admission(admission_path,registry_path,registry_sha,req)
        dataset=c.read(dataset_path,req['dataset_sha256'])
        extracted=c.extract(dataset,req['expected_loci'],req['selection_sha256'])
        conf=c.confidence(extracted,delta,req['radius_steps'])
        extracted_sha=c.sha(c.canonical(extracted));conf_sha=c.sha(c.canonical(conf))
        inv=c.inverse_request(req,conf,request_sha,extracted_sha,conf_sha)
        inv_sha=write_new(outdir/'INVERSE-REQUEST.json',inv)
        provider=c.load_provider();provider.read_request(outdir/'INVERSE-REQUEST.json',inv_sha)
        write_new(outdir/'EXTRACTION.json',extracted);write_new(outdir/'CONFIDENCE.json',conf)
        result={'schema':'phased-confidence-preparation-v1','status':'COMPLETE_PROTOCOL_PREPARATION' if admitted['classification']=='protocol_fixture' else 'COMPLETE_ADMITTED_PREPARATION','analysis_request_sha256':request_sha,'dataset_sha256':req['dataset_sha256'],'admission_sha256':req['admission_sha256'],'trusted_registry_sha256':registry_sha,'admission_classification':admitted['classification'],'scientific_premises':admitted['premises'],'extractor_sha256':c.sha(Path(c.__file__).read_bytes()),'provider_manifest_sha256':c.PROVIDER_MANIFEST_SHA,'extraction_sha256':extracted_sha,'confidence_sha256':conf_sha,'inverse_request_sha256':inv_sha,'data_confidence_certificate_issued':False,'ranked_histories':None,'recommended_history':None}
    except c.NotAdmitted as error:result=failure('NOT_ADMITTED',error,request_sha)
    except c.InputResource as error:result=failure('INPUT_RESOURCE_LIMIT',error,request_sha)
    except (OSError,ValueError,TypeError,KeyError,IndexError,ArithmeticError,RecursionError) as error:result=failure('EVIDENCE_INVALID',error,request_sha)
    write_new(outdir/'PREPARATION.json',result)
    return result

def failure(status,error,request_sha):
    return {'schema':'phased-confidence-preparation-v1','status':status,'analysis_request_sha256':request_sha,'error_type':type(error).__name__,'reason':str(error),'complete_extraction':False,'extraction_sha256':None,'confidence_sha256':None,'inverse_request_sha256':None,'data_confidence_certificate_issued':False,'ranked_histories':None,'recommended_history':None}
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser()
    for name in ('request','request-sha256','dataset','admission','registry','registry-sha256','output'):p.add_argument('--'+name,required=True)
    a=p.parse_args();print(json.dumps(prepare(a.request,a.request_sha256,a.dataset,a.admission,a.registry,a.registry_sha256,a.output),sort_keys=True,indent=2))
